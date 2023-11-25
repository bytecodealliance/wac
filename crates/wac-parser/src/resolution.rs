//! Module for resolving WAC documents.

use self::{encoding::Encoder, package::Package};
use crate::{lexer::Span, resolution::ast::AstResolver, Spanned};
use anyhow::Context;
use id_arena::{Arena, Id};
use indexmap::IndexMap;
use semver::Version;
use serde::{Serialize, Serializer};
use std::{
    collections::HashMap,
    fmt, fs,
    path::{Path, PathBuf},
};
use wit_parser::Resolve;

mod ast;
mod encoding;
mod package;
mod types;

pub use encoding::EncodingOptions;
pub use types::*;

fn serialize_arena<T, S>(arena: &Arena<T>, serializer: S) -> std::result::Result<S::Ok, S::Error>
where
    S: Serializer,
    T: Serialize,
{
    use serde::ser::SerializeSeq;

    let mut s = serializer.serialize_seq(Some(arena.len()))?;
    for (_, e) in arena.iter() {
        s.serialize_element(e)?;
    }

    s.end()
}

fn serialize_id_key_map<T, V, S>(
    map: &IndexMap<Id<T>, V>,
    serializer: S,
) -> std::result::Result<S::Ok, S::Error>
where
    S: Serializer,
    T: Serialize,
    V: Serialize,
{
    use serde::ser::SerializeMap;

    let mut s = serializer.serialize_map(Some(map.len()))?;
    for (k, v) in map {
        s.serialize_entry(&k.index(), v)?;
    }

    s.end()
}

fn serialize_id_value_map<K, T, S>(
    map: &IndexMap<K, Id<T>>,
    serializer: S,
) -> std::result::Result<S::Ok, S::Error>
where
    S: Serializer,
    K: Serialize,
    T: Serialize,
{
    use serde::ser::SerializeMap;

    let mut s = serializer.serialize_map(Some(map.len()))?;
    for (k, v) in map {
        s.serialize_entry(k, &v.index())?;
    }

    s.end()
}

fn serialize_id<T, S>(id: &Id<T>, serializer: S) -> std::result::Result<S::Ok, S::Error>
where
    S: Serializer,
    T: Serialize,
{
    id.index().serialize(serializer)
}

fn serialize_optional_id<T, S>(
    id: &Option<Id<T>>,
    serializer: S,
) -> std::result::Result<S::Ok, S::Error>
where
    S: Serializer,
    T: Serialize,
{
    match id {
        Some(id) => serializer.serialize_some(&id.index()),
        None => serializer.serialize_none(),
    }
}

/// Represents a kind of an extern item.
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub enum ExternKind {
    /// The item is an import.
    Import,
    /// The item is an export.
    Export,
}

impl fmt::Display for ExternKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Import => write!(f, "import"),
            Self::Export => write!(f, "export"),
        }
    }
}

struct InterfaceNameDisplay<'a>(Option<&'a str>);

impl fmt::Display for InterfaceNameDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Some(name) => write!(f, " for interface `{name}`"),
            None => Ok(()),
        }
    }
}

struct ParentPathDisplay<'a>(Option<&'static str>, &'a str);

impl fmt::Display for ParentPathDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Some(name) => {
                write!(f, "{name} `{path}` in ", path = self.1)
            }
            None => Ok(()),
        }
    }
}

/// Represents a resolution error.
#[derive(thiserror::Error, Debug)]
pub enum Error<'a> {
    /// An undefined name was encountered.
    #[error("undefined name `{name}`")]
    UndefinedName {
        /// The name that was undefined.
        name: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A duplicate name was encountered.
    #[error("`{name}` was previously defined at {path}:{line}:{column}", path = .path.display())]
    DuplicateName {
        /// The duplicate name.
        name: &'a str,
        /// The path to the source file.
        path: &'a Path,
        /// The line where the identifier was previously defined.
        line: usize,
        /// The column where the identifier was previously defined.
        column: usize,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// Duplicate interface export.
    #[error("duplicate interface export `{name}`{iface}", iface = InterfaceNameDisplay(*.interface_name))]
    DuplicateInterfaceExport {
        /// The name of the duplicate export.
        name: &'a str,
        /// The name of the interface.
        interface_name: Option<&'a str>,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// Duplicate world item.
    #[error("{kind} `{name}` conflicts with existing {kind} of the same name in world `{world}`")]
    DuplicateWorldItem {
        /// The extern kind of the item.
        kind: ExternKind,
        /// The name of the item.
        name: String,
        /// The name of the world.
        world: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// The name is not a function type or interface.
    #[error("`{name}` ({kind}) is not a function type or interface")]
    NotFuncOrInterface {
        /// The name that is not a function type or interface.
        name: &'a str,
        /// The kind of the item.
        kind: &'static str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// The name is not an interface.
    #[error("`{name}` ({kind}) is not an interface")]
    NotInterface {
        /// The name that is not an interface.
        name: &'a str,
        /// The kind of the item.
        kind: &'static str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// Duplicate name in a world include.
    #[error("duplicate `{name}` in world include `with` clause")]
    DuplicateWorldIncludeName {
        /// The name of the duplicate include.
        name: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// The name is not a world.
    #[error("`{name}` ({kind}) is not a world")]
    NotWorld {
        /// The name that is not a world.
        name: &'a str,
        /// The kind of the item.
        kind: &'static str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// Missing source item for `with` clause in world include.
    #[error("world `{world}` does not have an import or export named `{name}`")]
    MissingWorldInclude {
        /// The name of the world.
        world: &'a str,
        /// The name of the missing item.
        name: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A conflict was encountered in a world include.
    #[error("{kind} `{name}` from world `{from}` conflicts with {kind} of the same name in world `{to}`{hint}")]
    WorldIncludeConflict {
        /// The extern kind of the item.
        kind: ExternKind,
        /// The name of the item.
        name: String,
        /// The name of the source world.
        from: &'a str,
        /// The name of the target world.
        to: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
        /// The hint for the error.
        hint: &'static str,
    },
    /// A name is not a type defined in an interface.
    #[error("type `{name}` is not defined in interface `{interface_name}`")]
    UndefinedInterfaceType {
        /// The name of the type.
        name: &'a str,
        /// The name of the interface.
        interface_name: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A name is not a value type defined in an interface.
    #[error("`{name}` ({kind}) is not a value type in interface `{interface_name}`")]
    NotInterfaceValueType {
        /// The name that is not a value type.
        name: &'a str,
        /// The kind of the item.
        kind: &'static str,
        /// The name of the interface.
        interface_name: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A duplicate resource constructor was encountered.
    #[error("duplicate constructor for resource `{resource}`")]
    DuplicateResourceConstructor {
        /// The name of the resource.
        resource: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A duplicate resource method was encountered.
    #[error("duplicate method `{name}` for resource `{resource}`")]
    DuplicateResourceMethod {
        /// The name of the method.
        name: &'a str,
        /// The name of the resource.
        resource: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A duplicate variant case was encountered.
    #[error("duplicate case `{case}` for variant type `{name}`")]
    DuplicateVariantCase {
        /// The name of the case.
        case: &'a str,
        /// The name of the variant type.
        name: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A duplicate record field was encountered.
    #[error("duplicate field `{field}` for record type `{name}`")]
    DuplicateRecordField {
        /// The name of the field.
        field: &'a str,
        /// The name of the record type.
        name: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A duplicate enum case was encountered.
    #[error("duplicate case `{case}` for enum type `{name}`")]
    DuplicateEnumCase {
        /// The name of the case.
        case: &'a str,
        /// The name of the enum type.
        name: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A duplicate flag was encountered.
    #[error("duplicate flag `{flag}` for flags type `{name}`")]
    DuplicateFlag {
        /// The name of the flag.
        flag: &'a str,
        /// The name of the flags type.
        name: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// The name cannot be used as an alias type.
    #[error("`{name}` ({kind}) cannot be used in a type alias")]
    InvalidAliasType {
        /// The name that cannot be used as an alias type.
        name: &'a str,
        /// The kind of the item.
        kind: &'static str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// The name is not a function type.
    #[error("`{name}` ({kind}) is not a function type")]
    NotFuncType {
        /// The name that is not a function type.
        name: &'a str,
        /// The kind of the item.
        kind: &'static str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// The name is not a resource type.
    #[error("`{name}` ({kind}) is not a resource type")]
    NotResourceType {
        /// The name that is not a resource type.
        name: &'a str,
        /// The kind of the item.
        kind: &'static str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// The name is not a value type.
    #[error("`{name}` ({kind}) cannot be used as a value type")]
    NotValueType {
        /// The name that is not a value type.
        name: &'a str,
        /// The kind of the item.
        kind: &'static str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A duplicate function parameter was encountered.
    #[error("duplicate {kind} parameter `{name}`")]
    DuplicateParameter {
        /// The name of the parameter.
        name: &'a str,
        /// The kind of the function.
        kind: FuncKind,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A duplicate result was encountered.
    #[error("duplicate {kind} result `{name}`")]
    DuplicateResult {
        /// The name of the result.
        name: &'a str,
        /// The kind of the function.
        kind: FuncKind,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A borrow type was encountered in a function result.
    #[error("function result cannot recursively contain a borrow type")]
    BorrowInResult {
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A package failed to resolve.
    #[error("failed to resolve package `{name}`")]
    PackageResolutionFailure {
        /// The name of the package.
        name: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
        /// The underlying error.
        #[source]
        source: anyhow::Error,
    },
    /// A package failed to parse.
    #[error("failed to parse package `{name}`")]
    PackageParseFailure {
        /// The name of the package.
        name: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
        /// The underlying error.
        #[source]
        source: anyhow::Error,
    },
    /// An unknown package was encountered.
    #[error("unknown package `{name}`")]
    UnknownPackage {
        /// The name of the package.
        name: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A package is missing an export.
    #[error("{prev}package `{name}` has no export named `{export}`", prev = ParentPathDisplay(*.kind, .path))]
    PackageMissingExport {
        /// The name of the package.
        name: &'a str,
        /// The name of the export.
        export: &'a str,
        /// The kind of the item being accessed.
        kind: Option<&'static str>,
        /// The path to the current item.
        path: String,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A missing export in a package path was encountered.
    #[error("`{name}` ({kind}) has no export named `{export}`")]
    PackagePathMissingExport {
        /// The name that has no matching export.
        name: &'a str,
        /// The kind of the item.
        kind: &'static str,
        /// The name of the export.
        export: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A missing import on a component was encountered.
    #[error("component `{package}` has no import named `{import}`")]
    MissingComponentImport {
        /// The name of the package.
        package: &'a str,
        /// The name of the import.
        import: String,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A mismatched instantiation argument was encountered.
    #[error("mismatched instantiation argument `{name}`")]
    MismatchedInstantiationArg {
        /// The name of the argument.
        name: String,
        /// The span where the error occurred.
        span: Span<'a>,
        /// The source of the error.
        #[source]
        source: anyhow::Error,
    },
    /// A duplicate instantiation argument was encountered.
    #[error("duplicate instantiation argument `{name}`")]
    DuplicateInstantiationArg {
        /// The name of the argument.
        name: String,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A missing instantiation argument was encountered.
    #[error("missing instantiation argument `{name}` for package `{package}`")]
    MissingInstantiationArg {
        /// The name of the argument.
        name: String,
        /// The name of the package.
        package: &'a str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// An instantiation argument conflict was encountered.
    #[error("implicit instantiation argument `{name}` ({kind}) conflicts with an explicit import at {path}:{line}:{column}", path = .path.display())]
    InstantiationArgConflict {
        /// The name of the argument.
        name: String,
        /// The path of the source file.
        path: &'a Path,
        /// The kind of the argument.
        kind: &'static str,
        /// The line of the original instantiation.
        line: usize,
        /// The column of the original instantiation.
        column: usize,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// An explicitly imported item conflicts with an implicit import from an instantiation.
    #[error("import name `{name}` conflicts with an instance that was implicitly imported by the instantiation of `{package}` at {path}:{line}:{column}", path = .path.display())]
    ImportConflict {
        /// The name of the argument.
        name: String,
        /// The package that first introduced the import.
        package: &'a str,
        /// The path of the source file.
        path: &'a Path,
        /// The line of the original instantiation.
        line: usize,
        /// The column of the original instantiation.
        column: usize,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// An instantiation argument conflict was encountered.
    #[error("failed to merge instantiation argument `{name}` with an instance that was implicitly imported by the instantiation of `{package}` at {path}:{line}:{column}", path = .path.display())]
    InstantiationArgMergeFailure {
        /// The name of the argument.
        name: String,
        /// The name of the package that first introduced the import.
        package: &'a str,
        /// The path of the source file.
        path: &'a Path,
        /// The kind of the argument.
        kind: &'static str,
        /// The line of the original instantiation.
        line: usize,
        /// The column of the original instantiation.
        column: usize,
        /// The span where the error occurred.
        span: Span<'a>,
        /// The underlying merge error.
        #[source]
        source: anyhow::Error,
    },
    /// An unmergeable instantiation argument was encountered.
    #[error("implicit instantiation argument `{name}` ({kind}) conflicts with an implicitly imported argument from the instantiation of `{package}` at {path}:{line}:{column}", path = .path.display())]
    UnmergeableInstantiationArg {
        /// The name of the argument.
        name: String,
        /// The name of the package that first introduced the import.
        package: &'a str,
        /// The path of the source file.
        path: &'a Path,
        /// The kind of the argument.
        kind: &'static str,
        /// The line of the original instantiation.
        line: usize,
        /// The column of the original instantiation.
        column: usize,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// An access expression on an inaccessible value was encountered.
    #[error("a {kind} cannot be accessed")]
    Inaccessible {
        /// The kind of the item.
        kind: &'static str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// An access on an interface was encountered.
    #[error("an interface cannot be accessed")]
    InaccessibleInterface {
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// An instance is missing an export.
    #[error("the instance has no export named `{name}`")]
    MissingInstanceExport {
        /// The name of the export.
        name: String,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// An export requires a with clause.
    #[error("export statement requires a `with` clause as the export name cannot be inferred")]
    ExportRequiresWith {
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// An export conflicts with a definition.
    #[error("export `{name}` conflicts with {kind} definition at {path}:{line}:{column}{hint}", path = .path.display())]
    ExportConflict {
        /// The name of the export.
        name: String,
        /// The path of the source file.
        path: &'a Path,
        /// The kind of the definition.
        kind: &'static str,
        /// The line of the definition.
        line: usize,
        /// The column of the definition.
        column: usize,
        /// The hint of the error.
        hint: &'static str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A duplicate extern name was encountered.
    #[error("duplicate {kind} `{name}`")]
    DuplicateExternName {
        /// The name of the export.
        name: String,
        /// The kind of extern name.
        kind: ExternKind,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// An invalid extern name was encountered.
    #[error("{kind} name `{name}` is not valid")]
    InvalidExternName {
        /// The name of the export.
        name: String,
        /// The kind of extern.
        kind: ExternKind,
        /// The span where the error occurred.
        span: Span<'a>,
        /// The underlying validation error.
        #[source]
        source: anyhow::Error,
    },
    /// Cannot instantiate the package being defined.
    #[error("cannot instantiate the package being defined")]
    CannotInstantiateSelf {
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// A use of a type conflicts with an extern item.
    #[error("use of type `{name}` conflicts with an {kind} of the same name{hint}")]
    UseConflict {
        /// The name of the used type.
        name: &'a str,
        /// The extern kind of the conflicting item.
        kind: ExternKind,
        /// The hint for the error.
        hint: &'static str,
        /// The span where the error occurred.
        span: Span<'a>,
    },
}

impl Spanned for Error<'_> {
    fn span(&self) -> Span {
        match self {
            Error::UndefinedName { span, .. }
            | Error::DuplicateName { span, .. }
            | Error::DuplicateInterfaceExport { span, .. }
            | Error::DuplicateWorldItem { span, .. }
            | Error::NotFuncOrInterface { span, .. }
            | Error::NotInterface { span, .. }
            | Error::DuplicateWorldIncludeName { span, .. }
            | Error::NotWorld { span, .. }
            | Error::MissingWorldInclude { span, .. }
            | Error::WorldIncludeConflict { span, .. }
            | Error::UndefinedInterfaceType { span, .. }
            | Error::NotInterfaceValueType { span, .. }
            | Error::DuplicateResourceConstructor { span, .. }
            | Error::DuplicateResourceMethod { span, .. }
            | Error::DuplicateVariantCase { span, .. }
            | Error::DuplicateRecordField { span, .. }
            | Error::DuplicateEnumCase { span, .. }
            | Error::DuplicateFlag { span, .. }
            | Error::InvalidAliasType { span, .. }
            | Error::NotFuncType { span, .. }
            | Error::NotResourceType { span, .. }
            | Error::NotValueType { span, .. }
            | Error::DuplicateParameter { span, .. }
            | Error::DuplicateResult { span, .. }
            | Error::BorrowInResult { span }
            | Error::PackageResolutionFailure { span, .. }
            | Error::PackageParseFailure { span, .. }
            | Error::UnknownPackage { span, .. }
            | Error::PackageMissingExport { span, .. }
            | Error::PackagePathMissingExport { span, .. }
            | Error::MissingComponentImport { span, .. }
            | Error::MismatchedInstantiationArg { span, .. }
            | Error::DuplicateInstantiationArg { span, .. }
            | Error::MissingInstantiationArg { span, .. }
            | Error::InstantiationArgConflict { span, .. }
            | Error::ImportConflict { span, .. }
            | Error::InstantiationArgMergeFailure { span, .. }
            | Error::UnmergeableInstantiationArg { span, .. }
            | Error::Inaccessible { span, .. }
            | Error::InaccessibleInterface { span, .. }
            | Error::MissingInstanceExport { span, .. }
            | Error::ExportRequiresWith { span }
            | Error::ExportConflict { span, .. }
            | Error::DuplicateExternName { span, .. }
            | Error::InvalidExternName { span, .. }
            | Error::CannotInstantiateSelf { span }
            | Error::UseConflict { span, .. } => *span,
        }
    }
}

/// Represents a resolution result.
pub type ResolutionResult<'a, T> = std::result::Result<T, Error<'a>>;

/// A trait implemented by package resolvers.
///
/// This is used when resolving a document to resolve any referenced packages.
pub trait PackageResolver {
    /// Resolves a package name to the package bytes.
    ///
    /// Returns `Ok(None)` if the package could not be found.
    fn resolve(&self, name: &str, version: Option<&Version>) -> anyhow::Result<Option<Vec<u8>>>;
}

/// Used to resolve packages from the file system.
pub struct FileSystemPackageResolver {
    root: PathBuf,
    overrides: HashMap<String, PathBuf>,
}

impl FileSystemPackageResolver {
    /// Creates a new `FileSystemPackageResolver` with the given root directory.
    pub fn new(root: impl Into<PathBuf>, overrides: HashMap<String, PathBuf>) -> Self {
        Self {
            root: root.into(),
            overrides,
        }
    }
}

impl Default for FileSystemPackageResolver {
    fn default() -> Self {
        Self::new("deps", Default::default())
    }
}

impl PackageResolver for FileSystemPackageResolver {
    fn resolve(&self, name: &str, version: Option<&Version>) -> anyhow::Result<Option<Vec<u8>>> {
        if version.is_some() {
            anyhow::bail!("local dependency resolution does not support package versions");
        }

        let path = if let Some(path) = self.overrides.get(name) {
            if !path.is_file() {
                anyhow::bail!(
                    "local path `{path}` for package `{name}` does not exist",
                    path = path.display(),
                    name = name
                )
            }

            path.clone()
        } else {
            let mut path = self.root.clone();
            for segment in name.split(':') {
                path.push(segment);
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
        };

        // First check to see if a directory exists.
        // If so, then treat it as a textual WIT package.
        if path.is_dir() {
            log::debug!(
                "loading WIT package from directory `{path}`",
                path = path.display()
            );

            let mut resolve = Resolve::new();
            let (pkg, _) = resolve.push_dir(&path)?;

            return wit_component::encode(Some(true), &resolve, pkg)
                .with_context(|| {
                    format!(
                        "failed to encode WIT package from directory `{path}`",
                        path = path.display()
                    )
                })
                .map(Some);
        }

        if !path.is_file() {
            log::debug!("package `{path}` does not exist", path = path.display());
            return Ok(None);
        }

        log::debug!("loading package from `{path}`", path = path.display());
        let bytes = fs::read(&path)
            .with_context(|| format!("failed to read package `{path}`", path = path.display()))?;

        #[cfg(feature = "wat")]
        if path.extension().and_then(std::ffi::OsStr::to_str) == Some("wat") {
            let bytes = match wat::parse_bytes(&bytes) {
                Ok(std::borrow::Cow::Borrowed(_)) => bytes,
                Ok(std::borrow::Cow::Owned(wat)) => wat,
                Err(mut e) => {
                    e.set_path(path);
                    anyhow::bail!(e);
                }
            };

            return Ok(Some(bytes));
        }

        Ok(Some(bytes))
    }
}

/// Represents the kind of an item.
#[derive(Debug, Clone, Copy, Serialize, Hash, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub enum ItemKind {
    /// The item is a type.
    Type(Type),
    /// The item is a resource.
    Resource(#[serde(serialize_with = "serialize_id")] ResourceId),
    /// The item is a function.
    Func(#[serde(serialize_with = "serialize_id")] FuncId),
    /// The item is a component instance.
    Instance(#[serde(serialize_with = "serialize_id")] InterfaceId),
    /// The item is an instantiation of a package.
    Instantiation(#[serde(serialize_with = "serialize_id")] PackageId),
    /// The item is a component.
    Component(#[serde(serialize_with = "serialize_id")] WorldId),
    /// The item is a core module.
    Module(#[serde(serialize_with = "serialize_id")] ModuleId),
    /// The item is a value.
    Value(ValueType),
}

impl ItemKind {
    fn ty(&self) -> Option<Type> {
        match self {
            ItemKind::Type(ty) => Some(*ty),
            ItemKind::Func(id) => Some(Type::Func(*id)),
            ItemKind::Instance(id) => Some(Type::Interface(*id)),
            ItemKind::Component(id) => Some(Type::World(*id)),
            ItemKind::Module(id) => Some(Type::Module(*id)),
            ItemKind::Value(ty) => Some(Type::Value(*ty)),
            ItemKind::Resource(_) | ItemKind::Instantiation(_) => None,
        }
    }

    fn as_str(&self, definitions: &Definitions) -> &'static str {
        match self {
            ItemKind::Resource(_) => "resource",
            ItemKind::Func(_) => "function",
            ItemKind::Type(ty) => ty.as_str(definitions),
            ItemKind::Instance(_) | ItemKind::Instantiation(_) => "instance",
            ItemKind::Component(_) => "component",
            ItemKind::Module(_) => "module",
            ItemKind::Value(_) => "value",
        }
    }
}

/// Represents a item defining a type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Definition {
    /// The name of the type.
    pub name: String,
    /// The kind of the item.
    pub kind: ItemKind,
}

/// Represents an import item.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Import {
    /// The import name.
    pub name: String,
    /// The kind of the import.
    pub kind: ItemKind,
}

/// Represents an instance export alias item.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Alias {
    /// The instance item being aliased.
    #[serde(serialize_with = "serialize_id")]
    pub item: ItemId,
    /// The export name.
    pub export: String,
    /// The kind of the exported item.
    pub kind: ItemKind,
}

/// Represents an instantiated package item.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Instantiation {
    /// The package being instantiated.
    #[serde(serialize_with = "serialize_id")]
    pub package: PackageId,
    /// The arguments of the instantiation.
    #[serde(serialize_with = "serialize_id_value_map")]
    pub arguments: IndexMap<String, ItemId>,
}

/// Represents a composition item.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum Item {
    /// The item comes from a use statement.
    Use(ItemKind),
    /// The item comes from a local definition.
    Definition(Definition),
    /// The item comes from an import,
    Import(Import),
    /// The item comes from an instance alias.
    Alias(Alias),
    /// The item comes from an instantiation.
    Instantiation(Instantiation),
}

impl Item {
    /// Returns the kind of the item.
    pub fn kind(&self) -> ItemKind {
        match self {
            Self::Use(kind) => *kind,
            Self::Definition(definition) => definition.kind,
            Self::Import(import) => import.kind,
            Self::Alias(alias) => alias.kind,
            Self::Instantiation(instantiation) => ItemKind::Instantiation(instantiation.package),
        }
    }
}

/// An identifier for items in a composition.
pub type ItemId = Id<Item>;

/// An identifier for foreign packages in a composition.
pub type PackageId = Id<Package>;

/// Represents a composition.
///
/// A composition may be encoded into a WebAssembly component.
#[derive(Debug, Serialize, Default)]
#[serde(rename_all = "camelCase")]
pub struct Composition {
    /// The package name of the composition.
    pub package: String,
    /// The package version of the composition.
    pub version: Option<Version>,
    /// The definitions in the composition.
    pub definitions: Definitions,
    /// The foreign packages referenced in the composition.
    #[serde(serialize_with = "serialize_arena")]
    pub packages: Arena<Package>,
    /// The items in the composition.
    #[serde(serialize_with = "serialize_arena")]
    pub items: Arena<Item>,
    /// The map of import names to items.
    #[serde(serialize_with = "serialize_id_value_map")]
    pub imports: IndexMap<String, ItemId>,
    /// The map of export names to items.
    #[serde(serialize_with = "serialize_id_value_map")]
    pub exports: IndexMap<String, ItemId>,
}

impl Composition {
    /// Creates a new composition from an AST document.
    pub fn from_ast<'a>(
        document: &'a crate::ast::Document<'a>,
        resolver: Option<Box<dyn PackageResolver>>,
    ) -> ResolutionResult<'a, Self> {
        AstResolver::new(document).resolve(resolver)
    }

    /// Encode the composition into a WebAssembly component.
    pub fn encode(&self, options: EncodingOptions) -> anyhow::Result<Vec<u8>> {
        Encoder::new(self, options).encode()
    }
}
