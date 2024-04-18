//! A library for encoding and decoding WebAssembly compositions.

#![deny(missing_docs)]

use anyhow::Result;
use indexmap::IndexMap;
use miette::{GraphicalReportHandler, GraphicalTheme, NamedSource, Report};
use std::{
    collections::HashMap,
    io::IsTerminal,
    path::{Path, PathBuf},
};
use wac_parser::Document;
use wac_resolver::{packages, CommandError, Error, FileSystemPackageResolver};
use wac_types::BorrowedPackageKey;
use warg_client::Retry;

pub mod commands;

mod progress;

fn fmt_err(e: impl Into<Report>, path: &Path, source: &str) -> anyhow::Error {
    let mut s = String::new();
    let e = e.into();
    GraphicalReportHandler::new()
        .with_cause_chain()
        .with_theme(if std::io::stderr().is_terminal() {
            GraphicalTheme::unicode()
        } else {
            GraphicalTheme::unicode_nocolor()
        })
        .render_report(
            &mut s,
            e.with_source_code(NamedSource::new(path.to_string_lossy(), source.to_string()))
                .as_ref(),
        )
        .expect("failed to render diagnostic");
    anyhow::Error::msg(s)
}

/// Represents a package resolver used to resolve packages
/// referenced from a document.
///
/// The resolver first checks the file system for a matching package.
///
/// If it cannot find a matching package, it will check the registry.
pub struct PackageResolver {
    fs: FileSystemPackageResolver,
    registry: wac_resolver::RegistryPackageResolver,
}

impl PackageResolver {
    /// Creates a new package resolver.
    pub async fn new(
        dir: impl Into<PathBuf>,
        overrides: HashMap<String, PathBuf>,
        registry: Option<&str>,
        retry: Option<Retry>,
    ) -> Result<Self> {
        Ok(Self {
            fs: FileSystemPackageResolver::new(dir, overrides, false),
            registry: wac_resolver::RegistryPackageResolver::new(
                registry,
                Some(Box::new(progress::ProgressBar::new())),
                retry,
            )
            .await?,
        })
    }

    /// Resolve all packages referenced in the given document.
    pub async fn resolve<'a>(
        &self,
        document: &'a Document<'a>,
    ) -> Result<IndexMap<BorrowedPackageKey<'a>, Vec<u8>>, CommandError> {
        let mut keys = packages(document)?;

        // Next, we resolve as many of the packages from the file system as possible
        // and filter out the ones that were resolved.
        #[allow(unused_mut)]
        let mut packages = self.fs.resolve(&keys)?;
        keys.retain(|key, _| !packages.contains_key(key));

        // Next resolve the remaining packages from the registry
        // The registry resolver will error on missing package
        if !keys.is_empty() {
            let reg_packages = self.registry.resolve(&keys).await?;
            keys.retain(|key, _| !reg_packages.contains_key(key));
            packages.extend(reg_packages);
        }

        // At this point keys should be empty, otherwise we have an unknown package
        if let Some((key, span)) = keys.first() {
            return Err(CommandError::WacResolution(Error::UnknownPackage {
                name: key.name.to_string(),
                span: *span,
            }));
        }

        Ok(packages)
    }
}
