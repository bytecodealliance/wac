//! Modules for package resolvers.

use crate::Error as WacResolutionError;
use indexmap::IndexMap;
use miette::{Diagnostic, SourceSpan};
use thiserror::Error;
use wac_parser::{resolution::Error as WacError, Document};

mod fs;
mod registry;
mod visitor;

pub use fs::*;
pub use registry::*;
pub use visitor::*;
use wac_types::BorrowedPackageKey;
use warg_client::ClientError;

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
    /// An unknown package version was encountered.
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
    /// The requested package version has been yanked.
    #[error("version {version} of package `{name}` has been yanked")]
    PackageVersionYanked {
        /// The name of the package.
        name: String,
        /// The version of the package that has been yanked.
        version: semver::Version,
        /// The span where the error occurred.
        #[label(primary, "{version} has been yanked")]
        span: SourceSpan,
    },
    /// A package log was empty.
    #[error("a release for package `{name}` has not yet been published")]
    PackageLogEmpty {
        /// The name of the package.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "package `{name}` has no releases")]
        span: SourceSpan,
    },
    /// A failure occurred while updating logs from the registry.
    #[error("failed to update registry logs")]
    RegistryUpdateFailure {
        /// The underlying error.
        #[source]
        source: anyhow::Error,
    },
    /// A failure occurred while downloading content from the registry.
    #[error("failed to download content from the registry")]
    RegistryDownloadFailure {
        /// The underlying error.
        #[source]
        source: anyhow::Error,
    },
    /// A failure occurred while reading content from registry storage.
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

#[derive(Debug, Error)]
/// Error for WAC commands
pub enum CommandError {
    /// General errors
    #[error(transparent)]
    General(#[from] anyhow::Error),
    /// Serde errors
    #[error(transparent)]
    Serde(#[from] serde_json::Error),
    /// Wac resolution errors
    #[error(transparent)]
    WacResolution(#[from] WacResolutionError),
    /// Wac errors
    #[error(transparent)]
    Wac(#[from] WacError),
    /// Client Error
    #[error("warg client error ({0}): {1}")]
    WargClient(String, ClientError),
    /// Client Error With Hint
    #[error("warg client error with hint ({0}): {1}")]
    WargHint(String, ClientError),
}

/// Error from warg client
pub struct WargClientError(pub ClientError);

impl std::fmt::Debug for WargClientError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("WargClientError").field(&self.0).finish()
    }
}
