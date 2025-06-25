use super::Error;
use anyhow::Result;
use indexmap::IndexMap;
use miette::SourceSpan;
use wac_types::BorrowedPackageKey;
use wasm_pkg_client::{caching::FileCache, Config, PackageRef};
use wasm_pkg_core::resolver::{Dependency, DependencyResolver, RegistryPackage};

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
    resolver: Option<DependencyResolver<'static>>,
    config: Config,
    cache_dir: std::path::PathBuf,
    bar: Option<Box<dyn ProgressBar>>,
}

impl RegistryPackageResolver {
    /// Creates a new registry package resolver using the default
    /// client configuration file.
    ///
    /// If `url` is `None`, the default URL will be used.
    pub async fn new(url: Option<&str>, bar: Option<Box<dyn ProgressBar>>) -> Result<Self> {
        let config = Config::global_defaults().await?;
        Self::new_with_config(url, config, bar).await
    }

    /// Creates a new registry package resolver with the given configuration.
    ///
    /// If `url` is `None`, the default URL will be used.
    pub async fn new_with_config(
        url: Option<&str>,
        mut config: Config,
        bar: Option<Box<dyn ProgressBar>>,
    ) -> Result<Self> {
        if let Some(url) = url {
            let registry = url.parse()?;
            config.set_default_registry(Some(registry));
        }
        
        let cache_dir = std::env::temp_dir().join("wac-cache");
        let cache = FileCache::new(&cache_dir).await?;
        let resolver = DependencyResolver::new(Some(config.clone()), None, cache)?;
        
        Ok(Self {
            resolver: Some(resolver),
            config,
            cache_dir,
            bar,
        })
    }

    /// Creates a new DependencyResolver instance.
    pub async fn resolver(&self) -> Result<DependencyResolver<'static>, Error> {
        let cache = FileCache::new(&self.cache_dir).await
            .map_err(|e| Error::RegistryUpdateFailure { source: e })?;
        DependencyResolver::new(Some(self.config.clone()), None, cache)
            .map_err(|e| Error::RegistryUpdateFailure { source: e })
    }

    /// Resolves the provided package keys to packages.
    ///
    /// If the package isn't found, an error is returned.
    pub async fn resolve<'a>(
        &mut self,
        keys: &IndexMap<BorrowedPackageKey<'a>, SourceSpan>,
    ) -> Result<IndexMap<BorrowedPackageKey<'a>, Vec<u8>>, Error> {
        if let Some(bar) = self.bar.as_ref() {
            bar.init(keys.len());
            bar.println("Resolving", "packages from the registry");
        }

        let mut resolver = self.resolver.take().ok_or_else(|| {
            Error::RegistryUpdateFailure { 
                source: anyhow::anyhow!("Resolver has already been consumed") 
            }
        })?;

        // Convert WAC package keys to wasm-pkg-core dependencies
        for (key, span) in keys {
            let package_ref = key.name
                .parse::<PackageRef>()
                .map_err(|_| Error::InvalidPackageName {
                    name: key.name.to_string(),
                    span: *span,
                })?;

            let dependency = if let Some(version) = &key.version {
                Dependency::Package(RegistryPackage {
                    name: Some(package_ref.clone()),
                    version: format!("={}", version).parse().map_err(|_| Error::InvalidPackageName {
                        name: key.name.to_string(),
                        span: *span,
                    })?,
                    registry: None,
                })
            } else {
                Dependency::Package(RegistryPackage {
                    name: Some(package_ref.clone()),
                    version: "*".parse().unwrap(),
                    registry: None,
                })
            };

            resolver.add_dependency(&package_ref, &dependency).await
                .map_err(|e| Error::RegistryUpdateFailure { source: e })?;
        }

        // Resolve all dependencies
        let resolutions = resolver.resolve().await
            .map_err(|e| Error::RegistryUpdateFailure { source: e })?;

        if let Some(bar) = self.bar.as_ref() {
            bar.println("Downloading", "package content from the registry");
        }

        // Download packages and convert back to WAC format
        let mut packages = IndexMap::with_capacity(keys.len());
        for (key, span) in keys {
            let package_ref = key.name.parse::<PackageRef>().unwrap();
            
            if let Some(resolution) = resolutions.get(&package_ref) {
                let decoded = resolution.decode().await
                    .map_err(|e| Error::RegistryDownloadFailure { source: e })?;

                // Get the raw bytes
                let bytes = match &decoded {
                    wasm_pkg_core::resolver::DecodedDependency::Wasm { resolution, .. } => {
                        match resolution {
                            wasm_pkg_core::resolver::DependencyResolution::Registry(reg_res) => {
                                let mut reader = reg_res.fetch().await
                                    .map_err(|e| Error::RegistryDownloadFailure { source: e })?;
                                let mut buf = Vec::new();
                                tokio::io::AsyncReadExt::read_to_end(&mut reader, &mut buf).await
                                    .map_err(|e| Error::RegistryDownloadFailure { source: e.into() })?;
                                buf
                            },
                            wasm_pkg_core::resolver::DependencyResolution::Local(local_res) => {
                                tokio::fs::read(&local_res.path).await
                                    .map_err(|e| Error::RegistryContentFailure {
                                        path: local_res.path.clone(),
                                        source: e.into(),
                                    })?
                            },
                        }
                    },
                    wasm_pkg_core::resolver::DecodedDependency::Wit { resolution, package: _ } => {
                        // For WIT packages, we need to serialize them back to bytes
                        // For now, return the WIT source as bytes
                        match resolution {
                            wasm_pkg_core::resolver::DependencyResolution::Local(local_res) => {
                                tokio::fs::read(&local_res.path).await
                                    .map_err(|e| Error::RegistryContentFailure {
                                        path: local_res.path.clone(),
                                        source: e.into(),
                                    })?
                            },
                            _ => {
                                return Err(Error::RegistryDownloadFailure { 
                                    source: anyhow::anyhow!("WIT packages from registry not yet supported") 
                                });
                            }
                        }
                    },
                };

                packages.insert(*key, bytes);
                
                if let Some(bar) = self.bar.as_ref() {
                    bar.inc(1);
                    if let Some(version) = resolution.version() {
                        bar.println(
                            "Downloaded",
                            &format!("package `{}` v{}", key.name, version),
                        );
                    } else {
                        bar.println(
                            "Downloaded",
                            &format!("package `{}`", key.name),
                        );
                    }
                }
            } else {
                return Err(Error::PackageDoesNotExist {
                    name: key.name.to_string(),
                    span: *span,
                });
            }
        }

        if let Some(bar) = self.bar.as_ref() {
            bar.finish();
        }

        Ok(packages)
    }
}