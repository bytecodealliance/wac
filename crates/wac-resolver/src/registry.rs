use super::Error;
use anyhow::Result;
use futures::{stream::FuturesUnordered, StreamExt};
use indexmap::IndexMap;
use miette::SourceSpan;
use semver::{Version, VersionReq};
use std::{fs, path::Path, sync::Arc};
use wac_types::BorrowedPackageKey;
use wasm_pkg_client::{Config, PackageRef, Registry};

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

struct Client(wasm_pkg_client::Client);

impl std::ops::Deref for Client {
    type Target = &wasm_pkg_client::Client;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl Client {
async fn unwrap_version_or_latest(&self, package: &PackageRef version: Option<Version>) -> Result<Version, Error> {
        if let Some(version) = version {
            return Ok(version)
        }
        self.list_all_versions(package)

}
}



/// Used to resolve packages from a Warg registry.
///
/// Note that the registry will be locked for the lifetime of
/// the resolver.
pub struct RegistryPackageResolver {
    client: Arc<Client>,
    bar: Option<Box<dyn ProgressBar>>,
}

impl RegistryPackageResolver {
    /// Creates a new registry package resolver using the default
    /// client configuration file.
    ///
    /// If `url` is `None`, the default URL will be used.
    pub async fn new(url: Option<&str>, bar: Option<Box<dyn ProgressBar>>) -> Result<Self> {
        let mut config = Config::global_defaults().await?;
        Self::new_with_config(url, config, bar)
    }

    /// Creates a new registry package resolver with the given configuration.
    ///
    /// If `url` is `None`, the default URL will be used.
    pub fn new_with_config(
        url: Option<&str>,
        mut config: Config,
        bar: Option<Box<dyn ProgressBar>>,
    ) -> Result<Self> {
        let registry = url.map(|u| u.parse::<Registry>()).transpose()?;
        config.set_default_registry(registry);
        Ok(Self {
            client: Arc::new(Client::new(config)),
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
                    key.name
                        .parse::<PackageRef>()
                        .map_err(|_| Error::InvalidPackageName {
                            name: key.name.to_string(),
                            span: *span,
                        })?,
                    (key.version.cloned(), *span),
                ))
            })
            .collect::<Result<IndexMap<PackageRef, (Option<Version>, SourceSpan)>, Error>>()?;

        // fetch required package logs and return error if any not found
        if let Some(bar) = self.bar.as_ref() {
            bar.println("Updating", "package logs from the registry");
        }

        match self
            .client
            .fetch_packages(package_names_with_source_span.keys())
            .await
        {
            Ok(_) => {}
            Err(ClientError::PackageDoesNotExist { name, .. }) => {
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
            // download package content if not in cache
            bar.init(keys.len());
            bar.println("Downloading", "package content from the registry");
        }

        let mut tasks = FuturesUnordered::new();
        for (index, (package, (version, span))) in
            package_names_with_source_span.into_iter().enumerate()
        {
            let client = self.client.clone();
            tasks.push(tokio::spawn(async move {
                use wasm_pkg_client::Error::*;
                let err = match client.get_release(package, version).await {
                    Ok(release) =>
        Err(VersionNotFound(version)=>  {

                                    Error::PackageVersionDoesNotExist {
                                        name: name.to_string(),
                                        version,
                                        span,
                                    }
        }

                }
                Ok((
                    index,
                    if let Some(version) = version {
                        client
                            .download_exact(&package, &version)
                            .await
                            .map_err(|err| match err {
                                ClientError::PackageVersionDoesNotExist { name, version } => {
                                    Error::PackageVersionDoesNotExist {
                                        name: name.to_string(),
                                        version,
                                        span,
                                    }
                                }
                                err => Error::RegistryDownloadFailure { source: err.into() },
                            })?
                    } else {
                        client
                            .download(&package, &VersionReq::STAR)
                            .await
                            .map_err(|err| Error::RegistryDownloadFailure { source: err.into() })?
                            .ok_or_else(|| Error::PackageNoReleases {
                                name: package.to_string(),
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
}
