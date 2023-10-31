//! Module for resolving WAC documents.

use self::package::Package;
use crate::{
    ast::{self, InterfaceItem, WorldItem},
    lexer::Span,
    line_column, Spanned,
};
use anyhow::Context;
use id_arena::{Arena, Id};
use indexmap::{IndexMap, IndexSet};
use serde::{Serialize, Serializer};
use std::{
    collections::{hash_map, HashMap},
    fmt, fs,
    path::{Path, PathBuf},
};
use wit_parser::Resolve;

mod package;
mod types;

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

fn serialize_id_map<T, S>(
    map: &IndexMap<String, Id<T>>,
    serializer: S,
) -> std::result::Result<S::Ok, S::Error>
where
    S: Serializer,
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
        Some(i) => serializer.serialize_some(&i.index()),
        None => serializer.serialize_none(),
    }
}

/// Represents a kind of item in a world.
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub enum WorldItemKind {
    /// The item is an import.
    Import,
    /// The item is an export.
    Export,
}

impl fmt::Display for WorldItemKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            WorldItemKind::Import => write!(f, "import"),
            WorldItemKind::Export => write!(f, "export"),
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
        /// The kind of the item.
        kind: WorldItemKind,
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
        /// The kind of the item.
        kind: WorldItemKind,
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
            | Error::PackageResolutionFailure { span, .. }
            | Error::PackageParseFailure { span, .. }
            | Error::UnknownPackage { span, .. }
            | Error::PackageMissingExport { span, .. }
            | Error::PackagePathMissingExport { span, .. }
            | Error::MissingComponentImport { span, .. }
            | Error::MismatchedInstantiationArg { span, .. }
            | Error::DuplicateInstantiationArg { span, .. }
            | Error::MissingInstantiationArg { span, .. }
            | Error::Inaccessible { span, .. }
            | Error::InaccessibleInterface { span, .. }
            | Error::MissingInstanceExport { span, .. } => *span,
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
    fn resolve(&self, name: &str) -> anyhow::Result<Option<Vec<u8>>>;
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
    fn resolve(&self, name: &str) -> anyhow::Result<Option<Vec<u8>>> {
        let path = if let Some(path) = self.overrides.get(name) {
            if !path.exists() {
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
    /// The kind is a type.
    Type(Type),
    /// The kind is a function.
    Func(#[serde(serialize_with = "serialize_id")] FuncId),
    /// The kind is a component instance.
    Instance(#[serde(serialize_with = "serialize_id")] InterfaceId),
    /// The kind is an instantiation of a component.
    Instantiation(#[serde(serialize_with = "serialize_id")] WorldId),
    /// The kind is a component.
    Component(#[serde(serialize_with = "serialize_id")] WorldId),
    /// The kind is a core module.
    Module(#[serde(serialize_with = "serialize_id")] ModuleId),
    /// The kind is a value.
    Value(ValueType),
}

impl ItemKind {
    fn as_str(&self, definitions: &Definitions) -> &'static str {
        match self {
            ItemKind::Func(_) => "function",
            ItemKind::Type(ty) => ty.as_str(definitions),
            ItemKind::Instance(_) | ItemKind::Instantiation(_) => "instance",
            ItemKind::Component(_) => "component",
            ItemKind::Module(_) => "module",
            ItemKind::Value(_) => "value",
        }
    }
}

/// Represents the source of an item.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ItemSource {
    /// The item comes from a local definition.
    Definition,
    /// The item comes from a use statement.
    Use,
    /// The item comes from an import,
    Import {
        /// The import string to use.
        with: Option<String>,
    },
    /// The item comes from an alias.
    Alias {
        /// The instance being aliased.
        #[serde(serialize_with = "serialize_id")]
        item: ItemId,
        /// The export name.
        export: String,
    },
    /// The item comes from an instantiation.
    Instantiation {
        /// The arguments of the instantiation.
        #[serde(serialize_with = "serialize_id_map")]
        arguments: IndexMap<String, ItemId>,
    },
}

/// Represents an item in a resolved document.
#[derive(Debug, Clone, Serialize)]
pub struct Item {
    /// The kind of the item.
    pub kind: ItemKind,
    /// The source of the item.
    pub source: ItemSource,
}

/// Represents an identifier for an item.
pub type ItemId = Id<Item>;

/// An identifier for scopes.
pub type ScopeId = Id<Scope>;

/// Represents a scope for named items.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Scope {
    #[serde(serialize_with = "serialize_optional_id")]
    parent: Option<ScopeId>,
    #[serde(serialize_with = "serialize_id_map")]
    items: IndexMap<String, ItemId>,
}

impl Scope {
    /// Gets a named item from the scope.
    pub fn get(&self, name: &str) -> Option<ItemId> {
        self.items.get(name).copied()
    }

    /// Iterates all named items in the scope.
    pub fn iter(&self) -> impl Iterator<Item = ItemId> + '_ {
        self.items.values().copied()
    }
}

struct ResolutionState<'a> {
    document: &'a ast::Document<'a>,
    resolver: Option<Box<dyn PackageResolver>>,
    root_scope: ScopeId,
    current_scope: ScopeId,
    packages: HashMap<String, Package>,
    offsets: HashMap<ItemId, usize>,
    aliases: HashMap<(ItemId, String), ItemId>,
}

/// Represents a kind of function in the component model.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum FuncKind {
    /// The function is a "free" function (i.e. not associated with a resource).
    Free,
    /// The function is a method on a resource.
    Method,
    /// The function is a static method on a resource.
    Static,
    /// The function is a resource constructor.
    Constructor,
}

impl fmt::Display for FuncKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FuncKind::Free => write!(f, "function"),
            FuncKind::Method => write!(f, "method"),
            FuncKind::Static => write!(f, "static method"),
            FuncKind::Constructor => write!(f, "constructor"),
        }
    }
}

/// Represents a resolved document.
///
/// A resolution may be encoded to a WebAssembly component.
#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ResolvedDocument {
    /// The name of the package being resolved.
    pub package: String,
    /// The definitions in the resolution.
    pub definitions: Definitions,
    /// The items in the resolution.
    #[serde(serialize_with = "serialize_arena")]
    pub items: Arena<Item>,
    /// The name scopes in the resolution.
    #[serde(serialize_with = "serialize_arena")]
    pub scopes: Arena<Scope>,
}

impl ResolvedDocument {
    /// Creates a new resolved document from the given document.
    pub fn new<'a>(
        document: &'a ast::Document<'a>,
        package: impl Into<String>,
        resolver: Option<Box<dyn PackageResolver>>,
    ) -> ResolutionResult<'a, Self> {
        let mut scopes = Arena::new();
        let root_scope = scopes.alloc(Scope {
            parent: None,
            items: Default::default(),
        });

        let mut resolution = ResolvedDocument {
            package: package.into(),
            definitions: Default::default(),
            items: Default::default(),
            scopes,
        };

        let mut state = ResolutionState {
            document,
            resolver,
            root_scope,
            current_scope: root_scope,
            packages: Default::default(),
            offsets: Default::default(),
            aliases: Default::default(),
        };

        for stmt in &document.statements {
            match stmt {
                ast::Statement::Import(i) => resolution.import(&mut state, i)?,
                ast::Statement::Type(t) => resolution.type_statement(&mut state, t)?,
                ast::Statement::Let(l) => resolution.let_statement(&mut state, l)?,
                ast::Statement::Export(_) => todo!("implement export statements"),
            }
        }

        Ok(resolution)
    }

    /// Encode the resolved document as a WebAssembly component.
    pub fn encode(&self) -> ResolutionResult<Vec<u8>> {
        todo!("implement encoding")
    }

    fn get(&self, state: &ResolutionState, id: &ast::Ident) -> Option<ItemId> {
        let mut current = &self.scopes[state.current_scope];
        loop {
            if let Some(item) = current.get(id.string) {
                return Some(item);
            }

            current = &self.scopes[current.parent?];
        }
    }

    fn require<'a>(
        &self,
        state: &ResolutionState,
        id: &ast::Ident<'a>,
    ) -> ResolutionResult<'a, ItemId> {
        self.get(state, id).ok_or(Error::UndefinedName {
            name: id.string,
            span: id.span,
        })
    }

    fn push_scope(&mut self, state: &mut ResolutionState) {
        state.current_scope = self.scopes.alloc(Scope {
            parent: Some(state.current_scope),
            items: Default::default(),
        });
    }

    fn pop_scope(&mut self, state: &mut ResolutionState) -> ScopeId {
        let id = state.current_scope;
        state.current_scope = self.scopes[state.current_scope]
            .parent
            .expect("expected a scope to pop");
        id
    }

    fn register_name<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        id: ast::Ident<'a>,
        item: ItemId,
    ) -> ResolutionResult<'a, ()> {
        if let Some(prev) = self.scopes[state.current_scope]
            .items
            .insert(id.string.to_owned(), item)
        {
            let offset = state.offsets[&prev];
            let (line, column) = line_column(id.span.source(), offset);
            return Err(Error::DuplicateName {
                name: id.string,
                path: state.document.path,
                line,
                column,
                span: id.span,
            });
        }

        state.offsets.insert(item, id.span.start);

        Ok(())
    }

    fn import<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        stmt: &'a ast::ImportStatement<'a>,
    ) -> ResolutionResult<'a, ()> {
        let kind = match &stmt.ty {
            ast::ImportType::Package(p) => self.resolve_package_export(state, p)?,
            ast::ImportType::Func(ty) => {
                ItemKind::Func(self.func_type(state, &ty.params, &ty.results, FuncKind::Free)?)
            }
            ast::ImportType::Interface(i) => self.inline_interface(state, i)?,
            ast::ImportType::Ident(id) => self.items[self.require(state, id)?].kind,
        };

        // Promote function types, instance types, and component types to functions, instances, and components
        let kind = match kind {
            ItemKind::Type(Type::Func(id)) => ItemKind::Func(id),
            ItemKind::Type(Type::Interface(id)) => ItemKind::Instance(id),
            ItemKind::Type(Type::World(id)) => ItemKind::Component(id),
            _ => kind,
        };

        let id = self.items.alloc(Item {
            kind,
            source: ItemSource::Import {
                with: stmt.with.as_ref().map(|s| s.value.to_owned()),
            },
        });

        self.register_name(state, stmt.id, id)
    }

    fn type_statement<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        stmt: &'a ast::TypeStatement<'a>,
    ) -> ResolutionResult<'a, ()> {
        match stmt {
            ast::TypeStatement::Interface(i) => self.interface_decl(state, i),
            ast::TypeStatement::World(w) => self.world_decl(state, w),
            ast::TypeStatement::Type(t) => self.type_decl(state, t).map(|_| ()),
        }
    }

    fn let_statement<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        stmt: &'a ast::LetStatement<'a>,
    ) -> ResolutionResult<'a, ()> {
        let item = self.expr(state, &stmt.expr)?;
        self.register_name(state, stmt.id, item)
    }

    fn inline_interface<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        iface: &'a ast::InlineInterface<'a>,
    ) -> ResolutionResult<'a, ItemKind> {
        self.push_scope(state);

        let mut ty = Interface {
            id: None,
            exports: Default::default(),
            scope: Some(state.current_scope),
        };

        self.interface_items(state, None, &iface.items, &mut ty)?;

        self.pop_scope(state);

        Ok(ItemKind::Type(Type::Interface(
            self.definitions.interfaces.alloc(ty),
        )))
    }

    fn interface_decl<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        decl: &'a ast::InterfaceDecl<'a>,
    ) -> ResolutionResult<'a, ()> {
        self.push_scope(state);

        let mut ty = Interface {
            id: Some(format!(
                "{pkg}/{iface}",
                pkg = self.package,
                iface = decl.id.string,
            )),
            exports: Default::default(),
            scope: Some(state.current_scope),
        };

        self.interface_items(state, Some(decl.id.string), &decl.items, &mut ty)?;

        self.pop_scope(state);

        let ty = self.definitions.interfaces.alloc(ty);

        let id = self.items.alloc(Item {
            kind: ItemKind::Type(Type::Interface(ty)),
            source: ItemSource::Definition,
        });

        self.register_name(state, decl.id, id)
    }

    fn world_decl<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        decl: &'a ast::WorldDecl<'a>,
    ) -> ResolutionResult<'a, ()> {
        self.push_scope(state);

        let mut ty = World {
            imports: Default::default(),
            exports: Default::default(),
            scope: Some(state.current_scope),
        };

        self.world_body(state, decl.id.string, &decl.items, &mut ty)?;

        self.pop_scope(state);

        let ty = self.definitions.worlds.alloc(ty);

        let id = self.items.alloc(Item {
            kind: ItemKind::Type(Type::World(ty)),
            source: ItemSource::Definition,
        });

        self.register_name(state, decl.id, id)
    }

    fn interface_items<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        name: Option<&'a str>,
        items: &'a [InterfaceItem<'a>],
        ty: &mut Interface,
    ) -> ResolutionResult<'a, ()> {
        for item in items {
            match item {
                ast::InterfaceItem::Use(u) => self.use_type(state, u, &mut ty.exports, false)?,
                ast::InterfaceItem::Type(decl) => {
                    let kind = self.item_type_decl(state, decl)?;
                    let prev = ty
                        .exports
                        .insert(decl.id().string.into(), Extern::Kind(kind));
                    assert!(prev.is_none(), "duplicate type in scope");
                }
                ast::InterfaceItem::Export(e) => {
                    let kind = ItemKind::Func(self.func_type_ref(state, &e.ty, FuncKind::Free)?);
                    if ty
                        .exports
                        .insert(e.id.string.into(), Extern::Kind(kind))
                        .is_some()
                    {
                        return Err(Error::DuplicateInterfaceExport {
                            name: e.id.string,
                            interface_name: name,
                            span: e.id.span,
                        });
                    }
                }
            }
        }

        Ok(())
    }

    fn world_body<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        world: &'a str,
        items: &'a [WorldItem<'a>],
        ty: &mut World,
    ) -> ResolutionResult<'a, ()> {
        let mut includes = Vec::new();
        for item in items {
            match item {
                ast::WorldItem::Use(u) => self.use_type(state, u, &mut ty.imports, true)?,
                ast::WorldItem::Type(decl) => {
                    let kind = self.item_type_decl(state, decl)?;
                    let prev = ty
                        .exports
                        .insert(decl.id().string.into(), Extern::Kind(kind));
                    assert!(prev.is_none(), "duplicate type in scope");
                }
                ast::WorldItem::Import(i) => {
                    self.world_item_path(state, &i.path, WorldItemKind::Import, world, ty)?
                }
                ast::WorldItem::Export(e) => {
                    self.world_item_path(state, &e.path, WorldItemKind::Export, world, ty)?
                }
                ast::WorldItem::Include(i) => {
                    // We delay processing includes until after all other items have been processed
                    includes.push(i);
                }
            }
        }

        // Process the includes now that all imports and exports have been processed.
        // This allows us to detect conflicts only in explicitly defined items.
        for i in includes {
            self.world_include(state, i, world, ty)?;
        }

        Ok(())
    }

    fn world_item_path<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        path: &'a ast::WorldItemPath<'a>,
        kind: WorldItemKind,
        world: &'a str,
        ty: &mut World,
    ) -> ResolutionResult<'a, ()> {
        let (k, v) = match path {
            ast::WorldItemPath::Named(named) => {
                check_name(named.id.string, named.id.span, ty, world, kind)?;

                (
                    named.id.string.into(),
                    match &named.ty {
                        ast::ExternType::Ident(id) => {
                            let item = &self.items[self.require(state, id)?];
                            match item.kind {
                                ItemKind::Type(Type::Interface(id)) | ItemKind::Instance(id) => {
                                    ItemKind::Instance(id)
                                }
                                ItemKind::Type(Type::Func(id)) | ItemKind::Func(id) => {
                                    ItemKind::Func(id)
                                }
                                _ => {
                                    return Err(Error::NotFuncOrInterface {
                                        name: id.string,
                                        kind: item.kind.as_str(&self.definitions),
                                        span: id.span,
                                    });
                                }
                            }
                        }
                        ast::ExternType::Func(f) => ItemKind::Func(self.func_type(
                            state,
                            &f.params,
                            &f.results,
                            FuncKind::Free,
                        )?),
                        ast::ExternType::Interface(i) => self.inline_interface(state, i)?,
                    },
                )
            }
            ast::WorldItemPath::Ident(id) => {
                let item = &self.items[self.require(state, id)?];
                match item.kind {
                    ItemKind::Type(Type::Interface(iface_ty_id))
                    | ItemKind::Instance(iface_ty_id) => {
                        let iface_id = self.definitions.interfaces[iface_ty_id]
                            .id
                            .as_ref()
                            .expect("expected an interface id");
                        check_name(iface_id, id.span, ty, world, kind)?;
                        (iface_id.clone(), ItemKind::Instance(iface_ty_id))
                    }
                    _ => {
                        return Err(Error::NotInterface {
                            name: id.string,
                            kind: item.kind.as_str(&self.definitions),
                            span: id.span,
                        });
                    }
                }
            }

            ast::WorldItemPath::Package(p) => match self.resolve_package_export(state, p)? {
                ItemKind::Type(Type::Interface(id)) | ItemKind::Instance(id) => {
                    let name = self.definitions.interfaces[id]
                        .id
                        .as_ref()
                        .expect("expected an interface id");
                    check_name(name, p.span, ty, world, kind)?;
                    (name.clone(), ItemKind::Instance(id))
                }
                kind => {
                    return Err(Error::NotInterface {
                        name: p.span.as_str(),
                        kind: kind.as_str(&self.definitions),
                        span: p.span,
                    });
                }
            },
        };

        if kind == WorldItemKind::Import {
            ty.imports.insert(k, Extern::Kind(v));
        } else {
            ty.exports.insert(k, Extern::Kind(v));
        }

        return Ok(());

        fn check_name<'a>(
            name: &str,
            span: Span<'a>,
            ty: &World,
            world: &'a str,
            kind: WorldItemKind,
        ) -> ResolutionResult<'a, ()> {
            let exists: bool = if kind == WorldItemKind::Import {
                ty.imports.contains_key(name)
            } else {
                ty.exports.contains_key(name)
            };

            if exists {
                return Err(Error::DuplicateWorldItem {
                    kind,
                    name: name.to_owned(),
                    world,
                    span,
                });
            }

            Ok(())
        }
    }

    fn world_include<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        include: &ast::WorldInclude<'a>,
        world: &'a str,
        ty: &mut World,
    ) -> ResolutionResult<'a, ()> {
        let mut replacements = HashMap::new();
        for item in &include.with {
            let prev = replacements.insert(item.from.string, item);
            if prev.is_some() {
                return Err(Error::DuplicateWorldIncludeName {
                    name: item.from.string,
                    span: item.from.span,
                });
            }
        }

        let id = match &include.world {
            ast::WorldRef::Ident(id) => {
                let item = &self.items[self.require(state, id)?];
                match item.kind {
                    ItemKind::Type(Type::World(id)) | ItemKind::Component(id) => id,
                    kind => {
                        return Err(Error::NotWorld {
                            name: id.string,
                            kind: kind.as_str(&self.definitions),
                            span: id.span,
                        });
                    }
                }
            }
            ast::WorldRef::Package(path) => match self.resolve_package_export(state, path)? {
                ItemKind::Type(Type::World(id)) | ItemKind::Component(id) => id,
                kind => {
                    return Err(Error::NotWorld {
                        name: path.span.as_str(),
                        kind: kind.as_str(&self.definitions),
                        span: path.span,
                    });
                }
            },
        };

        let other = &self.definitions.worlds[id];
        for (name, item) in &other.imports {
            let name = replace_name(
                include,
                world,
                ty,
                name,
                WorldItemKind::Import,
                &mut replacements,
            )?;
            ty.imports.entry(name).or_insert(*item);
        }

        for (name, item) in &other.exports {
            let name = replace_name(
                include,
                world,
                ty,
                name,
                WorldItemKind::Export,
                &mut replacements,
            )?;
            ty.exports.entry(name).or_insert(*item);
        }

        if let Some(missing) = replacements.values().next() {
            return Err(Error::MissingWorldInclude {
                world: include.world.name(),
                name: missing.from.string,
                span: missing.from.span,
            });
        }

        return Ok(());

        fn replace_name<'a>(
            include: &ast::WorldInclude<'a>,
            world: &'a str,
            ty: &mut World,
            name: &str,
            kind: WorldItemKind,
            replacements: &mut HashMap<&str, &ast::WorldIncludeItem<'a>>,
        ) -> ResolutionResult<'a, String> {
            // Check for a id, which doesn't get replaced.
            if name.contains(':') {
                return Ok(name.to_owned());
            }

            let (name, span) = replacements
                .remove(name)
                .map(|i| (i.to.string, i.to.span))
                .unwrap_or_else(|| (name, include.world.span()));

            let exists = if kind == WorldItemKind::Import {
                ty.imports.contains_key(name)
            } else {
                ty.exports.contains_key(name)
            };

            if exists {
                return Err(Error::WorldIncludeConflict {
                    kind,
                    name: name.to_owned(),
                    from: include.world.name(),
                    to: world,
                    span,
                    hint: if !include.with.is_empty() {
                        ""
                    } else {
                        " (consider using a `with` clause to use a different name)"
                    },
                });
            }

            Ok(name.to_owned())
        }
    }

    fn use_type<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        use_type: &ast::Use<'a>,
        externs: &mut ExternMap,
        in_world: bool,
    ) -> ResolutionResult<'a, ()> {
        let (interface, name) = match &use_type.path {
            ast::UsePath::Package(path) => match self.resolve_package_export(state, path)? {
                ItemKind::Type(Type::Interface(id)) | ItemKind::Instance(id) => {
                    (id, path.span.as_str())
                }
                kind => {
                    return Err(Error::NotInterface {
                        name: path.span.as_str(),
                        kind: kind.as_str(&self.definitions),
                        span: path.span,
                    });
                }
            },
            ast::UsePath::Ident(id) => {
                let item = &self.items[self.require(state, id)?];
                match item.kind {
                    ItemKind::Type(Type::Interface(iface_ty_id))
                    | ItemKind::Instance(iface_ty_id) => (iface_ty_id, id.string),
                    kind => {
                        return Err(Error::NotInterface {
                            name: id.string,
                            kind: kind.as_str(&self.definitions),
                            span: id.span,
                        });
                    }
                }
            }
        };

        for item in &use_type.items {
            let ident = item.as_id.unwrap_or(item.id);
            let (index, _, ext) = self.definitions.interfaces[interface]
                .exports
                .get_full(item.id.string)
                .ok_or(Error::UndefinedInterfaceType {
                    name: item.id.string,
                    interface_name: name,
                    span: item.id.span,
                })?;

            let kind = ext.kind();
            match kind {
                ItemKind::Type(Type::Value(ty)) => {
                    let new_extern = Extern::Use {
                        interface,
                        export_index: index,
                        ty,
                    };

                    if in_world {
                        // A `use` of a type in a world will (transitively) import the interface that defines
                        // the type being used. This walks up the use chain, adding any necessary imports of
                        // the interfaces.
                        let mut cur = new_extern;
                        while let Extern::Use {
                            interface,
                            export_index,
                            ..
                        } = cur
                        {
                            let iface = &self.definitions.interfaces[interface];
                            let id = iface.id.as_deref().expect("interface must have an id");

                            if !externs.contains_key(id) {
                                externs.insert(
                                    id.to_owned(),
                                    Extern::Kind(ItemKind::Instance(interface)),
                                );
                            }

                            cur = iface.exports[export_index];
                        }
                    }

                    externs.insert(ident.string.into(), new_extern);

                    let id = self.items.alloc(Item {
                        kind,
                        source: ItemSource::Use,
                    });
                    self.register_name(state, ident, id)?;
                }
                _ => {
                    return Err(Error::NotInterfaceValueType {
                        name: item.id.string,
                        kind: kind.as_str(&self.definitions),
                        interface_name: name,
                        span: item.id.span,
                    });
                }
            }
        }

        Ok(())
    }

    fn type_decl<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        decl: &'a ast::TypeDecl,
    ) -> ResolutionResult<'a, ItemKind> {
        match decl {
            ast::TypeDecl::Variant(v) => self.variant_decl(state, v),
            ast::TypeDecl::Record(r) => self.record_decl(state, r),
            ast::TypeDecl::Flags(f) => self.flags_decl(state, f),
            ast::TypeDecl::Enum(e) => self.enum_decl(state, e),
            ast::TypeDecl::Alias(a) => self.type_alias(state, a),
        }
    }

    fn item_type_decl<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        decl: &'a ast::ItemTypeDecl,
    ) -> ResolutionResult<'a, ItemKind> {
        match decl {
            ast::ItemTypeDecl::Resource(r) => self.resource_decl(state, r),
            ast::ItemTypeDecl::Variant(v) => self.variant_decl(state, v),
            ast::ItemTypeDecl::Record(r) => self.record_decl(state, r),
            ast::ItemTypeDecl::Flags(f) => self.flags_decl(state, f),
            ast::ItemTypeDecl::Enum(e) => self.enum_decl(state, e),
            ast::ItemTypeDecl::Alias(a) => self.type_alias(state, a),
        }
    }

    fn resource_decl<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        decl: &ast::ResourceDecl<'a>,
    ) -> ResolutionResult<'a, ItemKind> {
        // Resources are allowed to be self-referential, so we need to allocate the resource
        // before we resolve the methods.
        let id = self.definitions.resources.alloc(Resource {
            methods: Default::default(),
        });
        let kind = ItemKind::Type(Type::Value(
            self.definitions.types.alloc(DefinedType::Resource(id)),
        ));
        let item_id = self.items.alloc(Item {
            kind,
            source: ItemSource::Definition,
        });

        self.register_name(state, decl.id, item_id)?;

        let mut methods: IndexMap<String, ResourceMethod> = Default::default();
        for method in &decl.methods {
            let (name, method, span) = match method {
                ast::ResourceMethod::Constructor(ast::Constructor { span, params, .. }) => (
                    "",
                    ResourceMethod {
                        kind: FuncKind::Constructor,
                        ty: self.func_type(
                            state,
                            params,
                            &ast::ResultList::Empty,
                            FuncKind::Constructor,
                        )?,
                    },
                    *span,
                ),
                ast::ResourceMethod::Method(ast::Method {
                    id, is_static, ty, ..
                }) => (
                    id.string,
                    ResourceMethod {
                        kind: if *is_static {
                            FuncKind::Static
                        } else {
                            FuncKind::Method
                        },
                        ty: self.func_type_ref(state, ty, FuncKind::Method)?,
                    },
                    id.span,
                ),
            };

            let prev = methods.insert(name.to_owned(), method);
            if prev.is_some() {
                return Err(if !name.is_empty() {
                    Error::DuplicateResourceMethod {
                        name,
                        resource: decl.id.string,
                        span,
                    }
                } else {
                    Error::DuplicateResourceConstructor {
                        resource: decl.id.string,
                        span,
                    }
                });
            }
        }

        self.definitions.resources[id].methods = methods;

        Ok(kind)
    }

    fn variant_decl<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        decl: &ast::VariantDecl<'a>,
    ) -> ResolutionResult<'a, ItemKind> {
        let mut cases = IndexMap::new();
        for case in &decl.cases {
            if cases
                .insert(
                    case.id.string.into(),
                    case.ty.as_ref().map(|ty| self.ty(state, ty)).transpose()?,
                )
                .is_some()
            {
                return Err(Error::DuplicateVariantCase {
                    case: case.id.string,
                    name: decl.id.string,
                    span: case.id.span,
                });
            }
        }

        let kind = ItemKind::Type(Type::Value(
            self.definitions
                .types
                .alloc(DefinedType::Variant(Variant { cases })),
        ));
        let id = self.items.alloc(Item {
            kind,
            source: ItemSource::Definition,
        });
        self.register_name(state, decl.id, id)?;
        Ok(kind)
    }

    fn record_decl<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        decl: &ast::RecordDecl<'a>,
    ) -> ResolutionResult<'a, ItemKind> {
        let mut fields = IndexMap::new();
        for field in &decl.fields {
            if fields
                .insert(field.id.string.into(), self.ty(state, &field.ty)?)
                .is_some()
            {
                return Err(Error::DuplicateRecordField {
                    field: field.id.string,
                    name: decl.id.string,
                    span: field.id.span,
                });
            }
        }

        let kind = ItemKind::Type(Type::Value(
            self.definitions
                .types
                .alloc(DefinedType::Record(Record { fields })),
        ));
        let id = self.items.alloc(Item {
            kind,
            source: ItemSource::Definition,
        });
        self.register_name(state, decl.id, id)?;
        Ok(kind)
    }

    fn flags_decl<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        decl: &ast::FlagsDecl<'a>,
    ) -> ResolutionResult<'a, ItemKind> {
        let mut flags = IndexSet::new();
        for flag in &decl.flags {
            if !flags.insert(flag.id.string.into()) {
                return Err(Error::DuplicateFlag {
                    flag: flag.id.string,
                    name: decl.id.string,
                    span: flag.id.span,
                });
            }
        }

        let kind = ItemKind::Type(Type::Value(
            self.definitions
                .types
                .alloc(DefinedType::Flags(Flags(flags))),
        ));
        let id = self.items.alloc(Item {
            kind,
            source: ItemSource::Definition,
        });
        self.register_name(state, decl.id, id)?;
        Ok(kind)
    }

    fn enum_decl<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        decl: &ast::EnumDecl<'a>,
    ) -> ResolutionResult<'a, ItemKind> {
        let mut cases = IndexSet::new();
        for case in &decl.cases {
            if !cases.insert(case.id.string.to_owned()) {
                return Err(Error::DuplicateEnumCase {
                    case: case.id.string,
                    name: decl.id.string,
                    span: case.id.span,
                });
            }
        }

        let kind = ItemKind::Type(Type::Value(
            self.definitions.types.alloc(DefinedType::Enum(Enum(cases))),
        ));
        let id = self.items.alloc(Item {
            kind,
            source: ItemSource::Definition,
        });

        self.register_name(state, decl.id, id)?;
        Ok(kind)
    }

    fn type_alias<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        alias: &ast::TypeAlias<'a>,
    ) -> ResolutionResult<'a, ItemKind> {
        let kind = match &alias.kind {
            ast::TypeAliasKind::Func(f) => ItemKind::Type(Type::Func(self.func_type(
                state,
                &f.params,
                &f.results,
                FuncKind::Free,
            )?)),
            ast::TypeAliasKind::Type(ty) => match ty {
                ast::Type::Ident(id) => {
                    let item = &self.items[self.require(state, id)?];
                    match item.kind {
                        ItemKind::Type(Type::Value(id)) => ItemKind::Type(Type::Value(
                            self.definitions
                                .types
                                .alloc(DefinedType::Alias(ValueType::Defined(id))),
                        )),
                        ItemKind::Type(Type::Func(id)) | ItemKind::Func(id) => {
                            ItemKind::Type(Type::Func(id))
                        }
                        _ => {
                            return Err(Error::InvalidAliasType {
                                name: id.string,
                                kind: item.kind.as_str(&self.definitions),
                                span: id.span,
                            });
                        }
                    }
                }
                _ => {
                    let ty = self.ty(state, ty)?;
                    ItemKind::Type(Type::Value(
                        self.definitions.types.alloc(DefinedType::Alias(ty)),
                    ))
                }
            },
        };

        let id = self.items.alloc(Item {
            kind,
            source: ItemSource::Definition,
        });

        self.register_name(state, alias.id, id)?;
        Ok(kind)
    }

    fn func_type_ref<'a>(
        &mut self,
        state: &ResolutionState<'a>,
        r: &ast::FuncTypeRef<'a>,
        kind: FuncKind,
    ) -> ResolutionResult<'a, FuncId> {
        match r {
            ast::FuncTypeRef::Func(ty) => self.func_type(state, &ty.params, &ty.results, kind),
            ast::FuncTypeRef::Ident(id) => {
                let item = &self.items[self.require(state, id)?];
                match item.kind {
                    ItemKind::Type(Type::Func(id)) | ItemKind::Func(id) => Ok(id),
                    _ => Err(Error::NotFuncType {
                        name: id.string,
                        kind: item.kind.as_str(&self.definitions),
                        span: id.span,
                    }),
                }
            }
        }
    }

    fn ty<'a>(
        &mut self,
        state: &ResolutionState<'a>,
        ty: &ast::Type<'a>,
    ) -> ResolutionResult<'a, ValueType> {
        match ty {
            ast::Type::U8 => Ok(ValueType::Primitive(PrimitiveType::U8)),
            ast::Type::S8 => Ok(ValueType::Primitive(PrimitiveType::S8)),
            ast::Type::U16 => Ok(ValueType::Primitive(PrimitiveType::U16)),
            ast::Type::S16 => Ok(ValueType::Primitive(PrimitiveType::S16)),
            ast::Type::U32 => Ok(ValueType::Primitive(PrimitiveType::U32)),
            ast::Type::S32 => Ok(ValueType::Primitive(PrimitiveType::S32)),
            ast::Type::U64 => Ok(ValueType::Primitive(PrimitiveType::U64)),
            ast::Type::S64 => Ok(ValueType::Primitive(PrimitiveType::S64)),
            ast::Type::Float32 => Ok(ValueType::Primitive(PrimitiveType::Float32)),
            ast::Type::Float64 => Ok(ValueType::Primitive(PrimitiveType::Float64)),
            ast::Type::Char => Ok(ValueType::Primitive(PrimitiveType::Char)),
            ast::Type::Bool => Ok(ValueType::Primitive(PrimitiveType::Bool)),
            ast::Type::String => Ok(ValueType::Primitive(PrimitiveType::String)),
            ast::Type::Tuple(v) => {
                let types = v
                    .iter()
                    .map(|ty| self.ty(state, ty))
                    .collect::<ResolutionResult<_>>()?;

                Ok(ValueType::Defined(
                    self.definitions.types.alloc(DefinedType::Tuple(types)),
                ))
            }
            ast::Type::List(ty) => {
                let ty = self.ty(state, ty)?;
                Ok(ValueType::Defined(
                    self.definitions.types.alloc(DefinedType::List(ty)),
                ))
            }
            ast::Type::Option(ty) => {
                let ty = self.ty(state, ty)?;
                Ok(ValueType::Defined(
                    self.definitions.types.alloc(DefinedType::Option(ty)),
                ))
            }
            ast::Type::Result { ok, err } => {
                let ok = ok.as_ref().map(|t| self.ty(state, t)).transpose()?;
                let err = err.as_ref().map(|t| self.ty(state, t)).transpose()?;
                Ok(ValueType::Defined(
                    self.definitions
                        .types
                        .alloc(DefinedType::Result { ok, err }),
                ))
            }
            ast::Type::Borrow(id) => {
                let item = &self.items[self.require(state, id)?];
                if let ItemKind::Type(Type::Value(id)) = item.kind {
                    if let DefinedType::Resource(id) = &self.definitions.types[id] {
                        return Ok(ValueType::Defined(
                            self.definitions.types.alloc(DefinedType::Borrow(*id)),
                        ));
                    }
                }

                Err(Error::NotResourceType {
                    name: id.string,
                    kind: item.kind.as_str(&self.definitions),
                    span: id.span,
                })
            }
            ast::Type::Ident(id) => {
                let item = &self.items[self.require(state, id)?];
                match item.kind {
                    ItemKind::Type(Type::Value(id)) => Ok(ValueType::Defined(id)),
                    _ => Err(Error::NotValueType {
                        name: id.string,
                        kind: item.kind.as_str(&self.definitions),
                        span: id.span,
                    }),
                }
            }
        }
    }

    fn func_type<'a>(
        &mut self,
        state: &ResolutionState<'a>,
        func_params: &[ast::NamedType<'a>],
        func_results: &ast::ResultList<'a>,
        kind: FuncKind,
    ) -> ResolutionResult<'a, FuncId> {
        let mut params = IndexMap::new();
        for param in func_params {
            if params
                .insert(param.id.string.into(), self.ty(state, &param.ty)?)
                .is_some()
            {
                return Err(Error::DuplicateParameter {
                    name: param.id.string,
                    kind,
                    span: param.id.span,
                });
            }
        }

        let results = match func_results {
            ast::ResultList::Empty => None,
            ast::ResultList::Named(results) => {
                let mut list = IndexMap::new();
                for result in results {
                    if list
                        .insert(result.id.string.to_owned(), self.ty(state, &result.ty)?)
                        .is_some()
                    {
                        return Err(Error::DuplicateResult {
                            name: result.id.string,
                            kind,
                            span: result.id.span,
                        });
                    }
                }
                Some(FuncResult::List(list))
            }
            ast::ResultList::Scalar(ty) => Some(FuncResult::Scalar(self.ty(state, ty)?)),
        };

        Ok(self.definitions.funcs.alloc(Func { params, results }))
    }

    fn resolve_package<'a, 'b>(
        &mut self,
        state: &'b mut ResolutionState<'a>,
        name: &'a str,
        span: Span<'a>,
    ) -> ResolutionResult<'a, &'b Package> {
        match state.packages.entry(name.to_owned()) {
            hash_map::Entry::Occupied(e) => Ok(e.into_mut()),
            hash_map::Entry::Vacant(e) => {
                log::debug!("resolving package `{name}`");
                match state
                    .resolver
                    .as_deref()
                    .and_then(|r| r.resolve(name).transpose())
                    .transpose()
                    .map_err(|e| Error::PackageResolutionFailure {
                        name,
                        span,
                        source: e,
                    })? {
                    Some(bytes) => Ok(e.insert(
                        Package::parse(&mut self.definitions, bytes).map_err(|e| {
                            Error::PackageParseFailure {
                                name,
                                span,
                                source: e,
                            }
                        })?,
                    )),
                    None => Err(Error::UnknownPackage { name, span }),
                }
            }
        }
    }

    fn resolve_package_export<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        path: &ast::PackagePath<'a>,
    ) -> ResolutionResult<'a, ItemKind> {
        // Check for reference to local item
        if path.name == self.package {
            return self.resolve_local_export(state, path);
        }

        let pkg = self.resolve_package(state, path.name, path.package_name_span())?;

        let mut current = 0;
        let mut parent_ty = None;
        let mut found = None;
        for (i, (segment, _)) in path.segment_spans().enumerate() {
            current = i;

            // Look up the first segment in the package definitions
            if i == 0 {
                found = pkg.definitions.get(segment).copied();
                continue;
            }

            // Otherwise, project into the parent based on the current segment
            let export = match found.unwrap() {
                // The parent is an interface or instance
                ItemKind::Type(Type::Interface(id)) | ItemKind::Instance(id) => {
                    self.definitions.interfaces[id]
                        .exports
                        .get(segment)
                        .map(Extern::kind)
                }
                // The parent is a world or component or component instantiation
                ItemKind::Type(Type::World(id))
                | ItemKind::Component(id)
                | ItemKind::Instantiation(id) => self.definitions.worlds[id]
                    .exports
                    .get(segment)
                    .map(Extern::kind),
                _ => None,
            };

            parent_ty = found.map(|kind| kind.as_str(&self.definitions));
            found = export;
            if found.is_none() {
                break;
            }
        }

        found.ok_or_else(|| {
            let segments = path.segment_spans().enumerate();
            let mut prev_path = String::new();
            for (i, (segment, span)) in segments {
                if i == current {
                    return Error::PackageMissingExport {
                        name: path.span.as_str(),
                        export: segment,
                        kind: parent_ty,
                        path: prev_path,
                        span,
                    };
                }

                if !prev_path.is_empty() {
                    prev_path.push('/');
                }

                prev_path.push_str(segment);
            }

            unreachable!("path segments should never be empty")
        })
    }

    fn resolve_local_export<'a>(
        &self,
        state: &ResolutionState,
        path: &ast::PackagePath<'a>,
    ) -> ResolutionResult<'a, ItemKind> {
        log::debug!("resolving local path `{path}`", path = path.span.as_str());

        let mut segments = path.segment_spans();
        let (segment, span) = segments.next().unwrap();
        let item = &self.items[self.scopes[state.root_scope].get(segment).ok_or({
            Error::UndefinedName {
                name: segment,
                span,
            }
        })?];

        let mut current = segment;
        let mut kind = item.kind;
        for (segment, span) in segments {
            let exports = match kind {
                ItemKind::Type(Type::Interface(id)) | ItemKind::Instance(id) => {
                    &self.definitions.interfaces[id].exports
                }
                ItemKind::Type(Type::World(id)) | ItemKind::Component(id) => {
                    &self.definitions.worlds[id].exports
                }
                _ => {
                    return Err(Error::PackagePathMissingExport {
                        name: current,
                        kind: kind.as_str(&self.definitions),
                        export: segment,
                        span,
                    });
                }
            };

            kind = exports.get(segment).map(Extern::kind).ok_or_else(|| {
                Error::PackagePathMissingExport {
                    name: current,
                    kind: kind.as_str(&self.definitions),
                    export: segment,
                    span,
                }
            })?;

            current = segment;
        }

        Ok(kind)
    }

    fn expr<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        expr: &'a ast::Expr,
    ) -> ResolutionResult<'a, ItemId> {
        let mut item = self.primary_expr(state, &expr.primary)?;

        for expr in &expr.postfix {
            item = self.postfix_expr(state, item, expr)?;
        }

        Ok(item)
    }

    fn primary_expr<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        expr: &'a ast::PrimaryExpr<'a>,
    ) -> ResolutionResult<'a, ItemId> {
        match expr {
            ast::PrimaryExpr::New(e) => self.new_expr(state, e),
            ast::PrimaryExpr::Nested(e) => self.expr(state, &e.0),
            ast::PrimaryExpr::Ident(i) => Ok(self.require(state, i)?),
        }
    }

    fn new_expr<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        expr: &'a ast::NewExpr<'a>,
    ) -> ResolutionResult<'a, ItemId> {
        let pkg = self.resolve_package(state, expr.package.name, expr.package.span)?;
        let ty = pkg.ty;
        let require_all = !expr.ellipsis;

        let mut arguments: IndexMap<String, ItemId> = Default::default();
        for arg in &expr.arguments {
            let (name, item, span) = match arg {
                ast::InstantiationArgument::Named(arg) => {
                    self.named_instantiation_arg(state, arg, ty)?
                }
                ast::InstantiationArgument::Ident(id) => {
                    self.ident_instantiation_arg(state, id, ty)?
                }
            };

            let world = &self.definitions.worlds[ty];
            let expected =
                world
                    .imports
                    .get(&name)
                    .ok_or_else(|| Error::MissingComponentImport {
                        package: expr.package.span.as_str(),
                        import: name.clone(),
                        span,
                    })?;

            SubtypeChecker::new(&self.definitions)
                .is_subtype(expected.kind(), self.items[item].kind)
                .map_err(|e| Error::MismatchedInstantiationArg {
                    name: name.clone(),
                    span,
                    source: e,
                })?;

            let prev = arguments.insert(name.clone(), item);
            if prev.is_some() {
                return Err(Error::DuplicateInstantiationArg { name, span });
            }
        }

        if require_all {
            let world = &self.definitions.worlds[ty];
            if let Some((missing, _)) = world
                .imports
                .iter()
                .find(|(n, _)| !arguments.contains_key(*n))
            {
                return Err(Error::MissingInstantiationArg {
                    name: missing.clone(),
                    package: expr.package.span.as_str(),
                    span: expr.package.span,
                });
            }
        }

        Ok(self.items.alloc(Item {
            kind: ItemKind::Instantiation(ty),
            source: ItemSource::Instantiation { arguments },
        }))
    }

    fn named_instantiation_arg<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        arg: &'a ast::NamedInstantiationArgument<'a>,
        world: WorldId,
    ) -> ResolutionResult<'a, (String, ItemId, Span<'a>)> {
        let item = self.expr(state, &arg.expr)?;

        let name = match &arg.name {
            ast::InstantiationArgumentName::Ident(ident) => Self::find_matching_interface_name(
                ident.string,
                &self.definitions.worlds[world].imports,
            )
            .unwrap_or(ident.string),
            ast::InstantiationArgumentName::String(name) => name.value,
        };

        Ok((name.to_owned(), item, arg.name.span()))
    }

    fn ident_instantiation_arg<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        ident: &ast::Ident<'a>,
        world: WorldId,
    ) -> ResolutionResult<'a, (String, ItemId, Span<'a>)> {
        let item_id = self.require(state, ident)?;
        let item = &self.items[item_id];
        let world = &self.definitions.worlds[world];

        // If the item is an instance with an id, try the id.
        if let ItemKind::Instance(id) = item.kind {
            if let Some(id) = &self.definitions.interfaces[id].id {
                if world.imports.contains_key(id.as_str()) {
                    return Ok((id.clone(), item_id, ident.span));
                }
            }
        }

        // If the item comes from an import or an alias, try the name associated with it
        match &item.source {
            ItemSource::Import { with: Some(name) } | ItemSource::Alias { export: name, .. } => {
                if world.imports.contains_key(name) {
                    return Ok((name.clone(), item_id, ident.span));
                }
            }
            _ => {}
        }

        // Fall back to searching for a matching interface name, provided it is not ambiguous
        // For example, match `foo:bar/baz` if `baz` is the identifier and the only match
        if let Some(name) = Self::find_matching_interface_name(ident.string, &world.imports) {
            return Ok((name.to_owned(), item_id, ident.span));
        }

        // Finally default to the id itself
        Ok((ident.string.to_owned(), item_id, ident.span))
    }

    fn find_matching_interface_name<'a>(name: &str, externs: &'a ExternMap) -> Option<&'a str> {
        // If the given name exists directly, don't treat it as an interface name
        if externs.contains_key(name) {
            return None;
        }

        // Fall back to searching for a matching interface name, provided it is not ambiguous
        // For example, match `foo:bar/baz` if `baz` is the identifier and the only match
        let mut matches = externs.iter().filter(|(n, _)| match n.rfind('/') {
            Some(start) => {
                let mut n = &n[start + 1..];
                if let Some(index) = n.find('@') {
                    n = &n[..index];
                }
                n == name
            }
            None => false,
        });

        let (name, _) = matches.next()?;
        if matches.next().is_some() {
            // More than one match, the name is ambiguous
            return None;
        }

        Some(name)
    }

    fn postfix_expr<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        item: ItemId,
        expr: &ast::PostfixExpr<'a>,
    ) -> ResolutionResult<'a, ItemId> {
        match expr {
            ast::PostfixExpr::Access(expr) => {
                let exports = self.instance_exports(item, expr.id.span)?;
                let name = Self::find_matching_interface_name(expr.id.string, exports)
                    .unwrap_or(expr.id.string)
                    .to_owned();
                self.access_expr(state, item, name, expr.id.span)
            }
            ast::PostfixExpr::NamedAccess(expr) => {
                self.access_expr(state, item, expr.string.value.to_owned(), expr.string.span)
            }
        }
    }

    fn instance_exports<'a>(
        &self,
        item: ItemId,
        span: Span<'a>,
    ) -> ResolutionResult<'a, &ExternMap> {
        match self.items[item].kind {
            ItemKind::Instance(id) => Ok(&self.definitions.interfaces[id].exports),
            ItemKind::Instantiation(id) => Ok(&self.definitions.worlds[id].exports),
            ItemKind::Type(Type::Interface(_)) => Err(Error::InaccessibleInterface { span }),
            kind => Err(Error::Inaccessible {
                kind: kind.as_str(&self.definitions),
                span,
            }),
        }
    }

    fn access_expr<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        item: ItemId,
        name: String,
        span: Span<'a>,
    ) -> ResolutionResult<'a, ItemId> {
        let exports = self.instance_exports(item, span)?;
        let kind =
            exports
                .get(&name)
                .map(Extern::kind)
                .ok_or_else(|| Error::MissingInstanceExport {
                    name: name.clone(),
                    span,
                })?;

        match state.aliases.entry((item, name.clone())) {
            hash_map::Entry::Occupied(e) => Ok(*e.get()),
            hash_map::Entry::Vacant(e) => {
                let id = self.items.alloc(Item {
                    kind,
                    source: ItemSource::Alias { item, export: name },
                });
                Ok(*e.insert(id))
            }
        }
    }
}
