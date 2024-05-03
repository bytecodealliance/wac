use super::Error;
use anyhow::Result;
use futures::{stream::FuturesUnordered, StreamExt};
use indexmap::IndexMap;
use miette::SourceSpan;
use secrecy::Secret;
use semver::{Version, VersionReq};
use std::{fs, path::Path, sync::Arc};
use wac_types::BorrowedPackageKey;
use warg_client::{Client, ClientError, Config, FileSystemClient, RegistryUrl};
use warg_credentials::keyring::get_auth_token;
use warg_protocol::registry::PackageName;

/// Implemented by progress bars.
///
/// This is used to abstract a UI for the registry resolver.
pub trait ProgressBar {
    /// Initializes the progress bar with the given count.
    fn init(&self, count: usize);

    /// Prints a message and then redraws the progress bar.
    fn println(&self, status: &str, msg: &str);

    /// Increments the progress bar by the given amount.
    fn inc(&self, delta: usize);

    // Finishes the progress bar.
    fn finish(&self);
}

/// Used to resolve packages from a Warg registry.
///
/// Note that the registry will be locked for the lifetime of
/// the resolver.
pub struct RegistryPackageResolver {
    client: Arc<FileSystemClient>,
    bar: Option<Box<dyn ProgressBar>>,
}

impl RegistryPackageResolver {
    /// Creates a new registry package resolver using the default
    /// client configuration file.
    ///
    /// If `url` is `None`, the default URL will be used.
    pub fn new(url: Option<&str>, bar: Option<Box<dyn ProgressBar>>) -> Result<Self> {
        let config = Config::from_default_file()?.unwrap_or_default();
        Ok(Self {
            client: Arc::new(Client::new_with_config(
                url,
                &config,
                Self::auth_token(&config, url)?,
            )?),
            bar,
        })
    }

    /// Creates a new registry package resolver with the given configuration.
    ///
    /// If `url` is `None`, the default URL will be used.
    pub fn new_with_config(
        url: Option<&str>,
        config: &Config,
        bar: Option<Box<dyn ProgressBar>>,
    ) -> Result<Self> {
        Ok(Self {
            client: Arc::new(Client::new_with_config(
                url,
                config,
                Self::auth_token(config, url)?,
            )?),
            bar,
        })
    }

    /// Resolves the provided package keys to packages.
    ///
    /// If the package isn't found, an error is returned.
    pub async fn resolve<'a>(
        &self,
        keys: &IndexMap<BorrowedPackageKey<'a>, SourceSpan>,
    ) -> Result<IndexMap<BorrowedPackageKey<'a>, Vec<u8>>, Error> {
        // parses into `PackageName` and maps back to `SourceSpan`
        let package_names_with_source_span = keys
            .iter()
            .map(|(key, span)| {
                Ok((
                    PackageName::new(key.name.to_string()).map_err(|_| {
                        Error::InvalidPackageName {
                            name: key.name.to_string(),
                            span: *span,
                        }
                    })?,
                    (key.version.cloned(), *span),
                ))
            })
            .collect::<Result<IndexMap<PackageName, (Option<Version>, SourceSpan)>, Error>>()?;

        // fetch required package logs and return error if any not found
        if let Some(bar) = self.bar.as_ref() {
            bar.init(1);
            bar.println("Updating", "package logs from the registry");
        }

        match self
            .client
            .fetch_packages(package_names_with_source_span.keys())
            .await
        {
            Ok(_) => {}
            Err(ClientError::PackageDoesNotExist { name }) => {
                return Err(Error::PackageDoesNotExist {
                    name: name.to_string(),
                    span: package_names_with_source_span.get(&name).unwrap().1,
                });
            }
            Err(err) => {
                return Err(Error::RegistryUpdateFailure { source: err.into() });
            }
        }

        if let Some(bar) = self.bar.as_ref() {
            bar.inc(1);
            bar.finish();

            // download package content if not in cache
            bar.init(keys.len());
            bar.println("Downloading", "package content from the registry");
        }

        let mut tasks = FuturesUnordered::new();
        for (index, (package_name, (version, span))) in
            package_names_with_source_span.into_iter().enumerate()
        {
            let client = self.client.clone();
            tasks.push(tokio::spawn(async move {
                Ok((
                    index,
                    if let Some(version) = version {
                        client
                            .download_exact(&package_name, &version)
                            .await
                            .map_err(|err| match err {
                                ClientError::PackageVersionDoesNotExist { name, version } => {
                                    Error::PackageVersionYankedOrDoesNotExist {
                                        name: name.to_string(),
                                        version,
                                        span,
                                    }
                                }
                                err => Error::RegistryDownloadFailure { source: err.into() },
                            })?
                    } else {
                        client
                            .download(&package_name, &VersionReq::STAR)
                            .await
                            .map_err(|err| Error::RegistryDownloadFailure { source: err.into() })?
                            .ok_or_else(|| Error::PackageNoReleases {
                                name: package_name.to_string(),
                                span,
                            })?
                    },
                ))
            }));
        }

        let mut packages = IndexMap::with_capacity(keys.len());
        let count = tasks.len();
        let mut finished = 0;

        while let Some(res) = tasks.next().await {
            let (index, download) = res.unwrap()?;

            finished += 1;

            let (key, _) = keys.get_index(index).unwrap();

            if let Some(bar) = self.bar.as_ref() {
                bar.inc(1);
                let BorrowedPackageKey { name, .. } = key;
                bar.println(
                    "Downloaded",
                    &format!("package `{name}` {version}", version = download.version),
                )
            }

            packages.insert(*key, Self::read_contents(&download.path)?);
        }

        assert_eq!(finished, count);

        if let Some(bar) = self.bar.as_ref() {
            bar.finish();
        }

        Ok(packages)
    }

    fn read_contents(path: &Path) -> Result<Vec<u8>, Error> {
        fs::read(path).map_err(|e| Error::RegistryContentFailure {
            path: path.to_path_buf(),
            source: e.into(),
        })
    }

    pub fn auth_token(config: &Config, url: Option<&str>) -> Result<Option<Secret<String>>> {
        if config.keyring_auth {
            return if let Some(url) = url {
                Ok(get_auth_token(&RegistryUrl::new(url)?)?)
            } else if let Some(url) = config.home_url.as_ref() {
                Ok(get_auth_token(&RegistryUrl::new(url)?)?)
            } else {
                Ok(None)
            };
        }

        Ok(None)
    }
}
