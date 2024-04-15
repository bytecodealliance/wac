use super::Error;
use anyhow::Result;
use futures::{stream::FuturesUnordered, StreamExt};
use indexmap::{IndexMap, IndexSet};
use miette::SourceSpan;
use secrecy::Secret;
use semver::{Comparator, Op, Version, VersionReq};
use std::{fs, path::Path, sync::Arc};
use wac_types::BorrowedPackageKey;
use warg_client::{
    storage::{ContentStorage, RegistryStorage},
    Client, ClientError, Config, FileSystemClient, RegistryUrl,
};
use warg_credentials::keyring::get_auth_token;
use warg_crypto::hash::AnyHash;

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
        // Start by fetching any required package logs
        self.fetch(keys).await?;

        // All the logs have been updated, now we need to see what content
        // is missing from local storage.
        let mut packages = IndexMap::new();
        let missing = self.find_missing_content(keys, &mut packages).await?;

        if !missing.is_empty() {
            if let Some(bar) = self.bar.as_ref() {
                bar.init(missing.len());
                bar.println("Downloading", "package content from the registry");
            }

            let mut tasks = FuturesUnordered::new();
            for (index, hash) in missing.keys().enumerate() {
                let client = self.client.clone();
                let hash = hash.clone();
                tasks.push(tokio::spawn(async move {
                    Ok((index, client.download_content(&hash).await?))
                }));
            }

            let count = tasks.len();
            let mut finished = 0;
            while let Some(res) = tasks.next().await {
                let (index, path) = res
                    .unwrap()
                    .map_err(|e| Error::RegistryDownloadFailure { source: e })?;

                let (hash, (version, set)) = missing.get_index(index).unwrap();
                log::debug!("downloaded content `{hash}`");

                finished += 1;

                if let Some(bar) = self.bar.as_ref() {
                    bar.inc(1);
                    let first = set.first().unwrap();
                    bar.println(
                        "Downloaded",
                        &format!("package `{name}` {version} ({hash})", name = first.name),
                    )
                }

                let contents = Self::read_contents(&path)?;
                for key in set {
                    packages.insert(*key, contents.clone());
                }
            }

            assert_eq!(finished, count);

            if let Some(bar) = self.bar.as_ref() {
                bar.finish();
            }
        }

        Ok(packages)
    }

    async fn fetch<'a>(
        &self,
        keys: &IndexMap<BorrowedPackageKey<'a>, SourceSpan>,
    ) -> Result<(), Error> {
        // First check if we already have the packages in client storage.
        // If not, we'll fetch the logs from the registry.
        let mut fetch = IndexMap::new();
        for (key, span) in keys {
            let id =
                key.name
                    .parse()
                    .map_err(|e: anyhow::Error| Error::PackageResolutionFailure {
                        name: key.name.to_string(),
                        span: *span,
                        source: e,
                    })?;

            // Load the package from client storage to see if we already
            // have a matching version present.
            if let Some(info) = self
                .client
                .registry()
                .load_package(self.client.get_warg_registry(), &id)
                .await
                .map_err(|e| Error::PackageResolutionFailure {
                    name: key.name.to_string(),
                    span: *span,
                    source: e,
                })?
            {
                if let Some(version) = key.version {
                    let req = VersionReq {
                        comparators: vec![Comparator {
                            op: Op::Exact,
                            major: version.major,
                            minor: Some(version.minor),
                            patch: Some(version.patch),
                            pre: version.pre.clone(),
                        }],
                    };

                    // Version already present, no need to fetch the log
                    if info.state.find_latest_release(&req).is_some() {
                        log::debug!(
                            "package log for `{name}` has a release version {version}",
                            name = key.name
                        );
                        continue;
                    }
                }
            }

            fetch.entry(id).or_insert_with(|| {
                log::debug!(
                    "fetching log for package `{name}` from the registry",
                    name = key.name
                );
                span
            });
        }

        // Fetch the logs
        if !fetch.is_empty() {
            if let Some(bar) = self.bar.as_ref() {
                bar.init(1);
                bar.println("Updating", "package logs from the registry");
            }

            match self.client.upsert(fetch.keys()).await {
                Ok(_) => {
                    if let Some(bar) = self.bar.as_ref() {
                        bar.inc(1);
                        bar.finish();
                    }
                }
                Err(ClientError::PackageDoesNotExist { name }) => {
                    return Err(Error::PackageDoesNotExist {
                        name: name.to_string(),
                        span: *fetch[&name],
                    })
                }
                Err(e) => {
                    return Err(Error::RegistryUpdateFailure { source: e.into() });
                }
            }
        }

        Ok(())
    }

    async fn find_missing_content<'a>(
        &self,
        keys: &IndexMap<BorrowedPackageKey<'a>, SourceSpan>,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> Result<IndexMap<AnyHash, (Version, IndexSet<BorrowedPackageKey<'a>>)>, Error> {
        let mut downloads: IndexMap<AnyHash, (Version, IndexSet<BorrowedPackageKey>)> =
            IndexMap::new();
        for (key, span) in keys {
            let id =
                key.name
                    .parse()
                    .map_err(|e: anyhow::Error| Error::PackageResolutionFailure {
                        name: key.name.to_string(),
                        span: *span,
                        source: e,
                    })?;

            let info = self
                .client
                .registry()
                .load_package(self.client.get_warg_registry(), &id)
                .await
                .map_err(|e| Error::PackageResolutionFailure {
                    name: key.name.to_string(),
                    span: *span,
                    source: e,
                })?
                .expect("package log should be present after fetching");

            let req = match key.version {
                Some(v) => VersionReq {
                    comparators: vec![Comparator {
                        op: Op::Exact,
                        major: v.major,
                        minor: Some(v.minor),
                        patch: Some(v.patch),
                        pre: v.pre.clone(),
                    }],
                },
                None => VersionReq::STAR,
            };

            let release = match info.state.find_latest_release(&req) {
                Some(release) if !release.yanked() => release,
                Some(release) => {
                    return Err(Error::PackageVersionYanked {
                        name: key.name.to_string(),
                        version: release.version.clone(),
                        span: *span,
                    });
                }
                None => {
                    if let Some(version) = key.version {
                        return Err(Error::UnknownPackageVersion {
                            name: key.name.to_string(),
                            version: version.clone(),
                            span: *span,
                        });
                    } else {
                        return Err(Error::PackageLogEmpty {
                            name: key.name.to_string(),
                            span: *span,
                        });
                    }
                }
            };

            let hash = release.content().unwrap();
            if let Some(path) = self.client.content().content_location(hash) {
                packages.insert(*key, Self::read_contents(&path)?);
            } else {
                log::debug!(
                    "downloading content for version {version} of package `{name}`",
                    name = key.name,
                    version = release.version
                );

                downloads
                    .entry(hash.clone())
                    .or_insert_with(|| (release.version.clone(), Default::default()))
                    .1
                    .insert(*key);
            }
        }

        Ok(downloads)
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
