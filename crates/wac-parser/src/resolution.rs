//! Module for resolving WAC documents.

use crate::ast::{Document, PackageName};
use anyhow::Result;
use id_arena::Arena;
use semver::Version;
use std::path::PathBuf;

/// Represents information about a resolved package.
pub struct Package {
    /// The version of the package.
    pub version: Version,
    /// The bytes of the package.
    pub bytes: Vec<u8>,
}

/// A trait implemented by package resolvers.
///
/// This is used when resolving a document to resolve any referenced packages.
pub trait PackageResolver {
    /// Resolves a package by name.
    ///
    /// Returns `Ok(None)` if the package could not be found.
    fn resolve(&self, name: &PackageName) -> Result<Option<Package>>;
}

/// Used to resolve packages from the file system.
pub struct FileSystemPackageResolver {
    root: PathBuf,
}

impl FileSystemPackageResolver {
    /// Creates a new `FileSystemPackageResolver` with the given root directory.
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }
}

impl PackageResolver for FileSystemPackageResolver {
    fn resolve(&self, name: &PackageName) -> Result<Option<Package>> {
        // TODO: probe for a `<root>/<namespace>+/<name>.wasm` file which
        // may be an encoded WIT package or a component.
        // Also probe for a `<root>/<namespace>+/<name>` directory and
        // parse it as a textual WIT package, encoding it.
        todo!()
    }
}

/// Used to resolve WAC documents.
pub struct DocumentResolver {
    resolver: Box<dyn PackageResolver>,
}

impl DocumentResolver {
    /// Creates a new `DocumentResolver`.
    pub fn new(resolver: Box<dyn PackageResolver>) -> Self {
        Self { resolver }
    }

    /// Resolves a document.
    pub fn resolve<'a>(&self, document: &'a Document<'a>) -> Result<ResolvedDocument<'a>> {
        // TODO:
        // Visit the AST and:
        //   * Register all names (imports, type statements, and let statements)
        //   * Register all type decls (type statements)
        //   * Resolve all package references (imports and new exprs)
        todo!()
    }
}

/// Represents a resolved document.
pub struct ResolvedDocument<'a> {
    // TODO: fill out this struct
    // types, interfaces, and worlds may either come from local
    // definitions or via the wasmparser validator type of
    // parsed foreign packages.
    document: &'a Document<'a>,
    types: Arena<()>,
    interfaces: Arena<()>,
    worlds: Arena<()>,
    packages: Arena<()>,
}

impl<'a> ResolvedDocument<'a> {
    /// Encode the resolved document as a WebAssembly component.
    pub fn encode(&self) -> Result<Vec<u8>> {
        // TODO: walk the AST and evaluate all statements,
        // encoding a WebAssembly component along the way.
        // this is where type checking occurs.
        todo!()
    }
}
