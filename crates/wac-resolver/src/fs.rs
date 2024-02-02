use super::Error;
use anyhow::{anyhow, Context, Result};
use indexmap::IndexMap;
use miette::SourceSpan;
use std::{collections::HashMap, fs, path::PathBuf, sync::Arc};
use wac_parser::PackageKey;

/// Used to resolve packages from the file system.
pub struct FileSystemPackageResolver {
    root: PathBuf,
    overrides: HashMap<String, PathBuf>,
    error_on_unknown: bool,
}

impl FileSystemPackageResolver {
    /// Creates a new file system resolver with the given root directory.
    pub fn new(
        root: impl Into<PathBuf>,
        overrides: HashMap<String, PathBuf>,
        error_on_unknown: bool,
    ) -> Self {
        Self {
            root: root.into(),
            overrides,
            error_on_unknown,
        }
    }

    /// Resolves the provided package keys to packages.
    pub fn resolve<'a>(
        &self,
        keys: &IndexMap<PackageKey<'a>, SourceSpan>,
    ) -> Result<IndexMap<PackageKey<'a>, Arc<Vec<u8>>>, Error> {
        let mut packages = IndexMap::new();
        for (key, span) in keys.iter() {
            let path = match self.overrides.get(key.name) {
                Some(path) if key.version.is_none() => {
                    if !path.is_file() {
                        return Err(Error::PackageResolutionFailure {
                            name: key.name.to_string(),
                            span: *span,
                            source: anyhow!(
                                "local path `{path}` for package `{name}` does not exist",
                                path = path.display(),
                                name = key.name
                            ),
                        });
                    }

                    path.clone()
                }
                _ => {
                    let mut path = self.root.clone();
                    for segment in key.name.split(':') {
                        path.push(segment);
                    }

                    if let Some(version) = key.version {
                        path.push(version.to_string());
                    }

                    // If the path is not a directory, use a `.wasm` or `.wat` extension
                    if !path.is_dir() {
                        path.set_extension("wasm");

                        #[cfg(feature = "wat")]
                        {
                            path.set_extension("wat");
                            if !path.exists() {
                                path.set_extension("wasm");
                            }
                        }
                    }

                    path
                }
            };

            // First check to see if a directory exists.
            // If so, then treat it as a textual WIT package.
            #[cfg(feature = "wit")]
            if path.is_dir() {
                log::debug!(
                    "loading WIT package from directory `{path}`",
                    path = path.display()
                );

                let mut resolve = wit_parser::Resolve::new();
                let (pkg, _) =
                    resolve
                        .push_dir(&path)
                        .map_err(|e| Error::PackageResolutionFailure {
                            name: key.name.to_string(),
                            span: *span,
                            source: e,
                        })?;

                packages.insert(
                    *key,
                    Arc::new(
                        wit_component::encode(Some(true), &resolve, pkg)
                            .with_context(|| {
                                format!(
                                    "failed to encode WIT package from directory `{path}`",
                                    path = path.display()
                                )
                            })
                            .map_err(|e| Error::PackageResolutionFailure {
                                name: key.name.to_string(),
                                span: *span,
                                source: e,
                            })?,
                    ),
                );

                continue;
            } else if path.extension().and_then(std::ffi::OsStr::to_str) == Some("wit") {
                return Err(Error::PackageResolutionFailure {
                    name: key.name.to_string(),
                    span: *span,
                    source: anyhow!(
                        "WIT packages must be directories, not files: `{path}`",
                        path = path.display()
                    ),
                });
            }

            if !path.is_file() {
                log::debug!(
                    "package `{key}` does not exist at `{path}`",
                    path = path.display()
                );
                if self.error_on_unknown {
                    return Err(Error::UnknownPackage {
                        name: key.name.to_string(),
                        span: *span,
                    });
                }
                continue;
            }

            log::debug!(
                "loading package `{key}` from `{path}`",
                path = path.display()
            );
            let bytes = fs::read(&path)
                .with_context(|| format!("failed to read package `{path}`", path = path.display()))
                .map_err(|e| Error::PackageResolutionFailure {
                    name: key.name.to_string(),
                    span: *span,
                    source: e,
                })?;

            #[cfg(feature = "wat")]
            if path.extension().and_then(std::ffi::OsStr::to_str) == Some("wat") {
                let bytes = match wat::parse_bytes(&bytes) {
                    Ok(std::borrow::Cow::Borrowed(_)) => bytes,
                    Ok(std::borrow::Cow::Owned(wat)) => wat,
                    Err(mut e) => {
                        e.set_path(path);
                        return Err(Error::PackageResolutionFailure {
                            name: key.name.to_string(),
                            span: *span,
                            source: anyhow!(e),
                        });
                    }
                };

                packages.insert(*key, Arc::new(bytes));
                continue;
            }

            packages.insert(*key, Arc::new(bytes));
        }

        Ok(packages)
    }
}

impl Default for FileSystemPackageResolver {
    fn default() -> Self {
        Self::new("deps", Default::default(), true)
    }
}
