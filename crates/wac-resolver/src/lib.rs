//! Modules for package resolvers.

use indexmap::IndexMap;
use miette::{Diagnostic, SourceSpan};
use wac_parser::Document;

mod fs;
#[cfg(feature = "registry")]
mod registry;
mod visitor;

pub use fs::*;
#[cfg(feature = "registry")]
pub use registry::*;
pub use visitor::*;
use wac_types::BorrowedPackageKey;

/// Represents a package resolution error.
#[derive(thiserror::Error, Diagnostic, Debug)]
#[diagnostic(code("failed to resolve document"))]
pub enum Error {
    /// An unknown package was encountered.
    #[error("unknown package `{name}`")]
    UnknownPackage {
        /// The name of the package.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "unknown package `{name}`")]
        span: SourceSpan,
    },
    /// An invalid package name was encountered.
    #[error("invalid package name `{name}`")]
    InvalidPackageName {
        /// The name of the package.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "invalid package name `{name}`")]
        span: SourceSpan,
    },
    /// An unknown package version was encountered.
    #[cfg(feature = "registry")]
    #[error("version {version} of package `{name}` does not exist")]
    UnknownPackageVersion {
        /// The name of the package.
        name: String,
        /// The version of the package that does not exist.
        version: semver::Version,
        /// The span where the error occurred.
        #[label(primary, "unknown package version `{version}`")]
        span: SourceSpan,
    },
    /// Cannot instantiate the package being defined.
    #[error("cannot instantiate the package being defined")]
    CannotInstantiateSelf {
        /// The span where the error occurred.
        #[label(primary, "cannot instantiate self")]
        span: SourceSpan,
    },
    /// Cannot instantiate the package being defined.
    #[error("package `{name}` does not exist in the registry")]
    PackageDoesNotExist {
        /// The name of the package that does not exist.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "package `{name}` does not exist")]
        span: SourceSpan,
    },
    /// The requested package version has been yanked or does not exist.
    #[cfg(feature = "registry")]
    #[error("version {version} of package `{name}` has been yanked or does not exist")]
    PackageVersionYankedOrDoesNotExist {
        /// The name of the package.
        name: String,
        /// The version of the package.
        version: semver::Version,
        /// The span where the error occurred.
        #[label(primary, "{version} has been yanked or does not exist")]
        span: SourceSpan,
    },
    /// A package has no releases.
    #[cfg(feature = "registry")]
    #[error("package `{name}` has no releases")]
    PackageNoReleases {
        /// The name of the package.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "package `{name}` has no releases")]
        span: SourceSpan,
    },
    /// A failure occurred while updating logs from the registry.
    #[cfg(feature = "registry")]
    #[error("failed to update registry logs")]
    RegistryUpdateFailure {
        /// The underlying error.
        #[source]
        source: anyhow::Error,
    },
    /// A failure occurred while downloading content from the registry.
    #[cfg(feature = "registry")]
    #[error("failed to download content from the registry")]
    RegistryDownloadFailure {
        /// The underlying error.
        #[source]
        source: anyhow::Error,
    },
    /// A failure occurred while reading content from registry storage.
    #[cfg(feature = "registry")]
    #[error("failed to read content path `{path}`", path = .path.display())]
    RegistryContentFailure {
        /// The path to the content.
        path: std::path::PathBuf,
        /// The underlying error.
        #[source]
        source: anyhow::Error,
    },
    /// A package failed to resolve.
    #[error("failed to resolve package `{name}`")]
    PackageResolutionFailure {
        /// The name of the package.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "package `{name}` failed to resolve")]
        span: SourceSpan,
        /// The underlying error.
        #[source]
        source: anyhow::Error,
    },
}

/// Builds a map of packages referenced in a document to the first span
/// which references the package.
pub fn packages<'a>(
    document: &'a Document<'a>,
) -> Result<IndexMap<BorrowedPackageKey<'a>, SourceSpan>, Error> {
    let mut keys = IndexMap::new();
    let mut visitor = PackageVisitor::new(|name, version, span| {
        if name == document.directive.package.name {
            return true;
        }

        if keys
            .insert(
                BorrowedPackageKey::from_name_and_version(name, version),
                span,
            )
            .is_none()
        {
            if let Some(version) = version {
                log::debug!("discovered reference to package `{name}` ({version})");
            } else {
                log::debug!("discovered reference to package `{name}`");
            }
        }

        true
    });

    visitor.visit(document)?;
    Ok(keys)
}
