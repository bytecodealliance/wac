//! Module for resolving WAC documents.

use self::{ast::AstResolver, encoding::Encoder, package::Package};
use id_arena::{Arena, Id};
use indexmap::IndexMap;
use miette::{Diagnostic, SourceSpan};
use semver::Version;
use serde::{Serialize, Serializer};
use std::{fmt, sync::Arc};

mod ast;
mod encoding;
mod package;
mod types;

pub use encoding::EncodingOptions;
pub use package::PackageKey;
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

struct InterfaceNameDisplay<'a>(&'a Option<String>);

impl fmt::Display for InterfaceNameDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            Some(name) => write!(f, " for interface `{name}`"),
            None => Ok(()),
        }
    }
}

struct ParentPathDisplay<'a>(&'a Option<String>, &'a str);

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

/// Represents an operation that may be performed on an instance.
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub enum InstanceOperation {
    /// The operation was an access of the form `.name` or `.["name"]`.
    Access,
    /// The operation was a spread of the form `...id` or `<expr>...`.
    Spread,
}

impl fmt::Display for InstanceOperation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Access => write!(f, "an access operation"),
            Self::Spread => write!(f, "a spread operation"),
        }
    }
}

/// Represents a resolution error.
#[derive(thiserror::Error, Diagnostic, Debug)]
#[diagnostic(code("failed to resolve document"))]
pub enum Error {
    /// An undefined name was encountered.
    #[error("undefined name `{name}`")]
    UndefinedName {
        /// The name that was undefined.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "undefined name `{name}`")]
        span: SourceSpan,
    },
    /// A duplicate name was encountered.
    #[error("`{name}` is already defined")]
    DuplicateName {
        /// The duplicate name.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "`{name}` redefined here")]
        span: SourceSpan,
        /// The span where the name was previously defined.
        #[label("`{name}` previously defined here")]
        previous: SourceSpan,
    },
    /// Duplicate interface export.
    #[error("duplicate interface export `{name}`{iface}", iface = InterfaceNameDisplay(.interface_name))]
    DuplicateInterfaceExport {
        /// The name of the duplicate export.
        name: String,
        /// The name of the interface.
        interface_name: Option<String>,
        /// The span where the error occurred.
        #[label(primary, "duplicate export `{name}`")]
        span: SourceSpan,
    },
    /// Duplicate world item.
    #[error("{kind} `{name}` conflicts with existing {kind} of the same name in world `{world}`")]
    DuplicateWorldItem {
        /// The extern kind of the item.
        kind: ExternKind,
        /// The name of the item.
        name: String,
        /// The name of the world.
        world: String,
        /// The span where the error occurred.
        #[label(primary, "conflicting name `{name}`")]
        span: SourceSpan,
    },
    /// The name is not a function type or interface.
    #[error("`{name}` ({kind}) is not a function type or interface")]
    NotFuncOrInterface {
        /// The name that is not a function type or interface.
        name: String,
        /// The kind of the item.
        kind: String,
        /// The span where the error occurred.
        #[label(primary, "`{name}` is not a function type or interface")]
        span: SourceSpan,
    },
    /// The name is not an interface.
    #[error("`{name}` ({kind}) is not an interface")]
    NotInterface {
        /// The name that is not an interface.
        name: String,
        /// The kind of the item.
        kind: String,
        /// The span where the error occurred.
        #[label(primary, "`{name}` is not an interface")]
        span: SourceSpan,
    },
    /// Duplicate name in a world include.
    #[error("duplicate `{name}` in world include `with` clause")]
    DuplicateWorldIncludeName {
        /// The name of the duplicate include.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "duplicate name `{name}`")]
        span: SourceSpan,
    },
    /// The name is not a world.
    #[error("`{name}` ({kind}) is not a world")]
    NotWorld {
        /// The name that is not a world.
        name: String,
        /// The kind of the item.
        kind: String,
        /// The span where the error occurred.
        #[label(primary, "`{name}` is not a world")]
        span: SourceSpan,
    },
    /// Missing source item for `with` clause in world include.
    #[error("world `{world}` does not have an import or export named `{name}`")]
    MissingWorldInclude {
        /// The name of the world.
        world: String,
        /// The name of the missing item.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "no import or export named `{name}`")]
        span: SourceSpan,
    },
    /// A conflict was encountered in a world include.
    #[error("{kind} `{name}` from world `{from}` conflicts with {kind} of the same name in world `{to}`")]
    WorldIncludeConflict {
        /// The extern kind of the item.
        kind: ExternKind,
        /// The name of the item.
        name: String,
        /// The name of the source world.
        from: String,
        /// The name of the target world.
        to: String,
        /// The span where the error occurred.
        #[label(primary, "conflicting name `{name}`")]
        span: SourceSpan,
        /// The help for the error.
        #[help]
        help: Option<String>,
    },
    /// A name is not a type defined in an interface.
    #[error("a type named `{name}` is not defined in interface `{interface_name}`")]
    UndefinedInterfaceType {
        /// The name of the type.
        name: String,
        /// The name of the interface.
        interface_name: String,
        /// The span where the error occurred.
        #[label(primary, "`{name}` is not a type in interface `{interface_name}`")]
        span: SourceSpan,
    },
    /// A name is not a value type defined in an interface.
    #[error("`{name}` ({kind}) is not a value type in interface `{interface_name}`")]
    NotInterfaceValueType {
        /// The name that is not a value type.
        name: String,
        /// The kind of the item.
        kind: String,
        /// The name of the interface.
        interface_name: String,
        /// The span where the error occurred.
        #[label(primary, "`{name}` is not a value type")]
        span: SourceSpan,
    },
    /// A duplicate resource constructor was encountered.
    #[error("duplicate constructor for resource `{resource}`")]
    DuplicateResourceConstructor {
        /// The name of the resource.
        resource: String,
        /// The span where the error occurred.
        #[label(primary, "duplicate constructor")]
        span: SourceSpan,
    },
    /// A duplicate resource method was encountered.
    #[error("duplicate method `{name}` for resource `{resource}`")]
    DuplicateResourceMethod {
        /// The name of the method.
        name: String,
        /// The name of the resource.
        resource: String,
        /// The span where the error occurred.
        #[label(primary, "duplicate method `{name}`")]
        span: SourceSpan,
    },
    /// A duplicate variant case was encountered.
    #[error("duplicate case `{case}` for variant type `{name}`")]
    DuplicateVariantCase {
        /// The name of the case.
        case: String,
        /// The name of the variant type.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "duplicate case `{case}`")]
        span: SourceSpan,
    },
    /// A duplicate record field was encountered.
    #[error("duplicate field `{field}` for record type `{name}`")]
    DuplicateRecordField {
        /// The name of the field.
        field: String,
        /// The name of the record type.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "duplicate field `{field}`")]
        span: SourceSpan,
    },
    /// A duplicate enum case was encountered.
    #[error("duplicate case `{case}` for enum type `{name}`")]
    DuplicateEnumCase {
        /// The name of the case.
        case: String,
        /// The name of the enum type.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "duplicate case `{case}`")]
        span: SourceSpan,
    },
    /// A duplicate flag was encountered.
    #[error("duplicate flag `{flag}` for flags type `{name}`")]
    DuplicateFlag {
        /// The name of the flag.
        flag: String,
        /// The name of the flags type.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "duplicate flag `{flag}`")]
        span: SourceSpan,
    },
    /// The name cannot be used as an alias type.
    #[error("`{name}` ({kind}) cannot be used in a type alias")]
    InvalidAliasType {
        /// The name that cannot be used as an alias type.
        name: String,
        /// The kind of the item.
        kind: String,
        /// The span where the error occurred.
        #[label(primary, "`{name}` cannot be aliased")]
        span: SourceSpan,
    },
    /// The name is not a function type.
    #[error("`{name}` ({kind}) is not a function type")]
    NotFuncType {
        /// The name that is not a function type.
        name: String,
        /// The kind of the item.
        kind: String,
        /// The span where the error occurred.
        #[label(primary, "`{name}` is not a function type")]
        span: SourceSpan,
    },
    /// The name is not a resource type.
    #[error("`{name}` ({kind}) is not a resource type")]
    NotResourceType {
        /// The name that is not a resource type.
        name: String,
        /// The kind of the item.
        kind: String,
        /// The span where the error occurred.
        #[label(primary, "`{name}` is not a resource type")]
        span: SourceSpan,
    },
    /// The name is not a value type.
    #[error("`{name}` ({kind}) cannot be used as a value type")]
    NotValueType {
        /// The name that is not a value type.
        name: String,
        /// The kind of the item.
        kind: String,
        /// The span where the error occurred.
        #[label(primary, "`{name}` not a value type")]
        span: SourceSpan,
    },
    /// A duplicate function parameter was encountered.
    #[error("duplicate {kind} parameter `{name}`")]
    DuplicateParameter {
        /// The name of the parameter.
        name: String,
        /// The kind of the function.
        kind: FuncKind,
        /// The span where the error occurred.
        #[label(primary, "duplicate parameter `{name}`")]
        span: SourceSpan,
    },
    /// A duplicate result was encountered.
    #[error("duplicate {kind} result `{name}`")]
    DuplicateResult {
        /// The name of the result.
        name: String,
        /// The kind of the function.
        kind: FuncKind,
        /// The span where the error occurred.
        #[label(primary, "duplicate result `{name}`")]
        span: SourceSpan,
    },
    /// A borrow type was encountered in a function result.
    #[error("function result cannot recursively contain a borrow type")]
    BorrowInResult {
        /// The span where the error occurred.
        #[label(primary, "borrow type in result")]
        span: SourceSpan,
    },
    /// An unknown package was encountered.
    #[error("unknown package `{name}`")]
    UnknownPackage {
        /// The name of the package.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "unknown package `{name}`")]
        span: SourceSpan,
    },
    /// A package failed to parse.
    #[error("failed to parse package `{name}`")]
    PackageParseFailure {
        /// The name of the package.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "package `{name}` failed to parse")]
        span: SourceSpan,
        /// The underlying error.
        #[source]
        source: anyhow::Error,
    },
    /// A package is missing an export.
    #[error("{prev}package `{name}` has no export named `{export}`", prev = ParentPathDisplay(.kind, .path))]
    PackageMissingExport {
        /// The name of the package.
        name: String,
        /// The name of the export.
        export: String,
        /// The kind of the item being accessed.
        kind: Option<String>,
        /// The path to the current item.
        path: String,
        /// The span where the error occurred.
        #[label(primary, "unknown export `{export}`")]
        span: SourceSpan,
    },
    /// A missing export in a package path was encountered.
    #[error("`{name}` ({kind}) has no export named `{export}`")]
    PackagePathMissingExport {
        /// The name that has no matching export.
        name: String,
        /// The kind of the item.
        kind: String,
        /// The name of the export.
        export: String,
        /// The span where the error occurred.
        #[label(primary, "unknown export `{export}`")]
        span: SourceSpan,
    },
    /// A missing import on a component was encountered.
    #[error("component `{package}` has no import named `{import}`")]
    MissingComponentImport {
        /// The name of the package.
        package: String,
        /// The name of the import.
        import: String,
        /// The span where the error occurred.
        #[label(primary, "unknown import `{import}`")]
        span: SourceSpan,
    },
    /// A mismatched instantiation argument was encountered.
    #[error("mismatched instantiation argument `{name}`")]
    MismatchedInstantiationArg {
        /// The name of the argument.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "mismatched argument `{name}`")]
        span: SourceSpan,
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
        #[label(primary, "duplicate argument `{name}`")]
        span: SourceSpan,
    },
    /// A missing instantiation argument was encountered.
    #[error("missing instantiation argument `{name}` for package `{package}`")]
    MissingInstantiationArg {
        /// The name of the argument.
        name: String,
        /// The name of the package.
        package: String,
        /// The span where the error occurred.
        #[label(primary, "missing argument `{name}`")]
        span: SourceSpan,
    },
    /// An instantiation argument conflict was encountered.
    #[error("implicit instantiation argument `{name}` ({kind}) conflicts with an explicit import")]
    InstantiationArgConflict {
        /// The name of the argument.
        name: String,
        /// The kind of the argument.
        kind: String,
        /// The span where the error occurred.
        #[label(primary, "conflicting instantiation here")]
        span: SourceSpan,
        /// The span where the explicit import occurred.
        #[label("explicit import here")]
        import: SourceSpan,
    },
    /// An explicitly imported item conflicts with an implicit import from an instantiation.
    #[error("import name `{name}` conflicts with an instance that was implicitly imported by an instantiation of `{package}`")]
    ImportConflict {
        /// The name of the argument.
        name: String,
        /// The package that first introduced the import.
        package: String,
        /// The span where the error occurred.
        #[label(primary, "conflicting import here")]
        span: SourceSpan,
        /// The span where the previous instantiation occurred.
        #[label("previous instantiation here")]
        instantiation: SourceSpan,
    },
    /// An instantiation argument conflict was encountered.
    #[error("failed to merge instantiation argument `{name}` with an instance that was implicitly imported by the instantiation of `{package}`")]
    InstantiationArgMergeFailure {
        /// The name of the argument.
        name: String,
        /// The name of the package that first introduced the import.
        package: String,
        /// The kind of the argument.
        kind: String,
        /// The span where the error occurred.
        #[label(primary, "conflicting instantiation here")]
        span: SourceSpan,
        /// The span where the previous instantiation occurred.
        #[label("previous instantiation here")]
        instantiation: SourceSpan,
        /// The underlying merge error.
        #[source]
        source: anyhow::Error,
    },
    /// An unmergeable instantiation argument was encountered.
    #[error("implicit instantiation argument `{name}` ({kind}) conflicts with an implicitly imported argument from the instantiation of `{package}`")]
    UnmergeableInstantiationArg {
        /// The name of the argument.
        name: String,
        /// The name of the package that first introduced the import.
        package: String,
        /// The kind of the argument.
        kind: String,
        /// The span where the error occurred.
        #[label(primary, "conflicting instantiation here")]
        span: SourceSpan,
        /// The span where the previous instantiation occurred.
        #[label("previous instantiation here")]
        instantiation: SourceSpan,
    },
    /// An operation was performed on something that was not an instance.
    #[error("an instance is required to perform {operation}")]
    NotAnInstance {
        /// The kind of item that was not an instance.
        kind: String,
        /// The operation that was performed.
        operation: InstanceOperation,
        /// The span where the error occurred.
        #[label(primary, "this evaluated to a {kind} when an instance was expected")]
        span: SourceSpan,
    },
    /// An instance is missing an export.
    #[error("the instance has no export named `{name}`")]
    MissingInstanceExport {
        /// The name of the export.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "unknown export `{name}`")]
        span: SourceSpan,
    },
    /// An export requires an `as`` clause.
    #[error("export statement requires an `as` clause as the export name cannot be inferred")]
    ExportRequiresAs {
        /// The span where the error occurred.
        #[label(primary, "an `as` clause is required")]
        span: SourceSpan,
    },
    /// An export conflicts with a definition.
    #[error("export `{name}` conflicts with {kind} definition")]
    ExportConflict {
        /// The name of the export.
        name: String,
        /// The kind of the definition.
        kind: String,
        /// The span where the error occurred.
        #[label(primary, "conflicting export of `{name}`")]
        span: SourceSpan,
        /// The span of the previous definition.
        #[label("previous definition is here")]
        definition: SourceSpan,
        /// The help of the error.
        #[help]
        help: Option<String>,
    },
    /// A duplicate extern name was encountered.
    #[error("duplicate {kind} `{name}`")]
    DuplicateExternName {
        /// The name of the export.
        name: String,
        /// The kind of extern name.
        kind: ExternKind,
        /// The span where the error occurred.
        #[label(primary, "duplicate {kind} name `{name}`")]
        span: SourceSpan,
        /// The span where the error occurred.
        #[label("previous {kind} here")]
        previous: SourceSpan,
        /// The help of the error.
        #[help]
        help: Option<String>,
    },
    /// An invalid extern name was encountered.
    #[error("{kind} name `{name}` is not valid")]
    InvalidExternName {
        /// The name of the export.
        name: String,
        /// The kind of extern.
        kind: ExternKind,
        /// The span where the error occurred.
        #[label(primary, "invalid name `{name}`")]
        span: SourceSpan,
        /// The underlying validation error.
        #[source]
        source: anyhow::Error,
    },
    /// A use of a type conflicts with an extern item.
    #[error("use of type `{name}` conflicts with an {kind} of the same name")]
    UseConflict {
        /// The name of the used type.
        name: String,
        /// The extern kind of the conflicting item.
        kind: ExternKind,
        /// The span where the error occurred.
        #[label(primary, "conflicting name `{name}`")]
        span: SourceSpan,
        /// The help message for the error.
        #[help]
        help: Option<String>,
    },
    /// A fill argument (`...`) was not the last argument.
    #[error("implicit import argument `...` must be the last argument")]
    FillArgumentNotLast {
        /// The span where the error occurred.
        #[label(primary, "must be last argument")]
        span: SourceSpan,
    },
    /// A spread instantiation argument did not match any import names.
    #[error("the instance has no matching exports for the remaining unsatisfied arguments")]
    SpreadInstantiationNoMatch {
        /// The span where the error occurred.
        #[label(primary, "no matching exports for the instance")]
        span: SourceSpan,
    },
    /// An export spread operation was performed and had no effect.
    #[error(
        "instance has no exports or all exports of the instance match previously exported names"
    )]
    SpreadExportNoEffect {
        /// The span where the error occurred.
        #[label(primary, "spreading the exports of this instance has no effect")]
        span: SourceSpan,
    },
}

/// Represents a resolution result.
pub type ResolutionResult<T> = std::result::Result<T, Error>;

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
        packages: IndexMap<PackageKey<'a>, Arc<Vec<u8>>>,
    ) -> ResolutionResult<Self> {
        AstResolver::new(document, packages).resolve()
    }

    /// Encode the composition into a WebAssembly component.
    pub fn encode(&self, options: EncodingOptions) -> anyhow::Result<Vec<u8>> {
        Encoder::new(self, options).encode()
    }
}
