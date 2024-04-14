//! Module for resolving WAC ASTs.

use crate::{ast, Document};
use indexmap::{IndexMap, IndexSet};
use miette::{Diagnostic, SourceSpan};
use semver::Version;
use std::{
    collections::{HashMap, HashSet},
    fmt,
};
use wac_graph::{
    types::{
        BorrowedPackageKey, DefinedType, Enum, ExternKind, Flags, FuncKind, FuncResult, FuncType,
        FuncTypeId, Interface, InterfaceId, ItemKind, Package, PackageKey, PrimitiveType, Record,
        Resource, ResourceAlias, ResourceId, SubtypeChecker, Type, UsedType, ValueType, Variant,
        World, WorldId,
    },
    CompositionGraph, DefineTypeError, EncodeError, EncodeOptions, ExportError, ImportError,
    InstantiationArgumentError, NodeId, NodeKind, PackageId, Processor,
};
use wasmparser::BinaryReaderError;

fn method_extern_name(resource: &str, name: &str, kind: FuncKind) -> String {
    match kind {
        FuncKind::Free => unreachable!("a resource method cannot be a free function"),
        FuncKind::Method => format!("[method]{resource}.{name}"),
        FuncKind::Static => format!("[static]{resource}.{name}"),
        FuncKind::Constructor => format!("[constructor]{resource}"),
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
    #[error("{prev}package `{package}` has no export named `{export}`", prev = ParentPathDisplay(.kind, .path))]
    PackageMissingExport {
        /// The package missing the export.
        package: String,
        /// The name of the missing export.
        export: String,
        /// The kind of the item missing the export.
        kind: Option<String>,
        /// The path to the item missing the export.
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
    /// An explicitly imported item conflicts with an item that was implicitly
    /// imported from an instantiation.
    #[error("import `{name}` conflicts with an item that was implicitly imported by an instantiation of `{package}`")]
    ImportConflict {
        /// The name of the argument.
        name: String,
        /// The package that first introduced the import.
        package: PackageKey,
        /// The span of the conflicting import.
        #[label(primary, "explicit import here")]
        import: SourceSpan,
        /// The span of the conflicting instantiation.
        #[label("conflicting instantiation here")]
        instantiation: SourceSpan,
    },
    /// An instantiation argument conflict was encountered.
    #[error(
        "failed to merge the type definition for implicit import `{name}` due to conflicting types"
    )]
    InstantiationArgMergeFailure {
        /// The name of the argument.
        name: String,
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
    /// A type declaration conflicts with an export of the same name
    #[error("type declaration `{name}` conflicts with a previous export of the same name")]
    DeclarationConflict {
        /// The name of the type.
        name: String,
        /// The span where the error occurred.
        #[label(primary, "conflicting type declaration `{name}`")]
        span: SourceSpan,
        /// The span of the previous export.
        #[label("previous export is here")]
        export: SourceSpan,
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
    /// An import is not in the target world.
    #[error("target world `{world}` does not have an import named `{name}`")]
    ImportNotInTarget {
        /// The import name.
        name: String,
        /// The target world.
        world: String,
        /// The span where the error occurred.
        #[label(primary, "cannot have an import named `{name}`")]
        span: SourceSpan,
    },
    /// Missing an export for the target world.
    #[error("target world `{world}` requires an export named `{name}`")]
    MissingTargetExport {
        /// The export name.
        name: String,
        /// The expected item kind.
        kind: String,
        /// The target world.
        world: String,
        /// The span where the error occurred.
        #[label(primary, "must export a {kind} named `{name}` to target this world")]
        span: SourceSpan,
    },
    /// An import or export has a mismatched type for the target world.
    #[error("{kind} `{name}` has a mismatched type for target world `{world}`")]
    TargetMismatch {
        /// The kind of mismatch.
        kind: ExternKind,
        /// The mismatched extern name.
        name: String,
        /// The target world.
        world: String,
        /// The span where the error occurred.
        #[label(primary, "mismatched type for {kind} `{name}`")]
        span: SourceSpan,
        /// The source of the error.
        #[source]
        source: anyhow::Error,
    },
    /// The encoding of the graph failed validation.
    #[error("the encoding of the graph failed validation")]
    ValidationFailure {
        /// The source of the validation error.
        #[source]
        source: BinaryReaderError,
    },
}

/// Represents a resolution result.
pub type ResolutionResult<T> = std::result::Result<T, Error>;

/// Represents a resolution of an WAC document.
pub struct Resolution<'a> {
    /// The document the resolution is from.
    document: &'a Document<'a>,
    /// The resolved composition graph.
    graph: CompositionGraph,
    /// The map from node id to import span.
    import_spans: HashMap<NodeId, SourceSpan>,
    /// The map from node id to instantiation span.
    instantiation_spans: HashMap<NodeId, SourceSpan>,
}

impl<'a> Resolution<'a> {
    /// Gets the document that was resolved.
    pub fn document(&self) -> &Document {
        self.document
    }

    /// Gets the resolved composition graph.
    pub fn graph(&self) -> &CompositionGraph {
        &self.graph
    }

    /// Encodes the resolution into a component.
    ///
    /// This method handles translating encoding errors into resolution
    /// errors that contain source span information.
    pub fn encode(&self, mut options: EncodeOptions) -> ResolutionResult<Vec<u8>> {
        options.processor = options.processor.or(Some(Processor {
            name: env!("CARGO_PKG_NAME"),
            version: env!("CARGO_PKG_VERSION"),
        }));

        self.graph.encode(options).map_err(|e| match e {
            EncodeError::ValidationFailure { source } => Error::ValidationFailure { source },
            EncodeError::GraphContainsCycle { .. } => panic!("AST contained a cycle"),
            EncodeError::ImplicitImportConflict {
                import,
                instantiation,
                package,
                name,
            } => Error::ImportConflict {
                name,
                package,
                import: self.import_spans[&import],
                instantiation: self.instantiation_spans[&instantiation],
            },
            EncodeError::ImportTypeMergeConflict {
                import,
                first,
                second,
                source,
            } => Error::InstantiationArgMergeFailure {
                name: import,
                span: self.instantiation_spans[&second],
                instantiation: self.instantiation_spans[&first],
                source,
            },
        })
    }

    /// Consumes the resolution and returns the underlying composition graph.
    ///
    /// Note that encoding the returned graph may still fail as a result of
    /// merging implicit instantiation arguments.
    pub fn into_graph(self) -> CompositionGraph {
        self.graph
    }
}

#[derive(Debug, Copy, Clone)]
enum Item {
    /// The item is a node in the composition graph.
    Node(NodeId),
    /// The item is a used type within an interface or world scope.
    Use(Type),
    /// The item is a type declaration not at root scope.
    ///
    /// At root scope, a type declaration is added to the graph.
    Type(Type),
}

impl Item {
    fn kind(&self, graph: &CompositionGraph) -> ItemKind {
        match self {
            Self::Node(id) => graph[*id].item_kind,
            Self::Use(ty) => ItemKind::Type(*ty),
            Self::Type(ty) => ItemKind::Type(*ty),
        }
    }

    fn node(&self) -> NodeId {
        match self {
            Self::Node(node) => *node,
            _ => panic!("the item is not a node"),
        }
    }
}

#[derive(Default)]
struct Scope(IndexMap<String, (Item, SourceSpan)>);

impl Scope {
    fn get(&self, name: &str) -> Option<(Item, SourceSpan)> {
        self.0.get(name).copied()
    }
}

#[derive(Default)]
struct State {
    scopes: Vec<Scope>,
    current: Scope,
    graph: CompositionGraph,
    instantiation_spans: HashMap<NodeId, SourceSpan>,
    import_spans: HashMap<NodeId, SourceSpan>,
    export_spans: HashMap<NodeId, SourceSpan>,
}

impl State {
    fn register_name(&mut self, id: ast::Ident, item: Item) -> ResolutionResult<()> {
        log::debug!(
            "registering name `{id}` in the current scope",
            id = id.string
        );

        if let Some((_, previous)) = self.current.0.insert(id.string.to_owned(), (item, id.span)) {
            return Err(Error::DuplicateName {
                name: id.string.to_owned(),
                span: id.span,
                previous,
            });
        }

        if let Item::Node(node) = item {
            // Use only the first name encountered for the node, ignoring
            // aliasing in the form of `let x = y;`
            if self.graph[node].name.is_none() {
                self.graph.set_node_name(node, id.string.to_owned());
            }
        }

        Ok(())
    }

    /// Gets an item by identifier from the root scope.
    fn root_item(&self, id: &ast::Ident) -> ResolutionResult<(Item, SourceSpan)> {
        self.root_scope()
            .get(id.string)
            .ok_or(Error::UndefinedName {
                name: id.string.to_owned(),
                span: id.span,
            })
    }

    /// Gets a node from the local (current) scope.
    fn local_item(&self, id: &ast::Ident) -> ResolutionResult<(Item, SourceSpan)> {
        self.current.get(id.string).ok_or(Error::UndefinedName {
            name: id.string.to_owned(),
            span: id.span,
        })
    }

    /// Gets an item by identifier from the local (current) scope or the root scope.
    fn local_or_root_item(&self, id: &ast::Ident) -> ResolutionResult<(Item, SourceSpan)> {
        if self.scopes.is_empty() {
            return self.local_item(id);
        }

        if let Some((item, span)) = self.current.get(id.string) {
            return Ok((item, span));
        }

        self.root_item(id)
    }

    fn push_scope(&mut self) {
        log::debug!("pushing new name scope");
        self.scopes.push(std::mem::take(&mut self.current));
    }

    fn pop_scope(&mut self) -> Scope {
        log::debug!("popping name scope");
        std::mem::replace(&mut self.current, self.scopes.pop().unwrap())
    }

    fn root_scope(&self) -> &Scope {
        self.scopes.first().unwrap_or(&self.current)
    }
}

pub(crate) struct AstResolver<'a>(&'a Document<'a>);

impl<'a> AstResolver<'a> {
    pub fn new(ast: &'a Document) -> Self {
        Self(ast)
    }

    pub fn resolve(
        mut self,
        mut packages: IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> ResolutionResult<Resolution<'a>> {
        let mut state = State::default();

        for stmt in &self.0.statements {
            match stmt {
                ast::Statement::Import(i) => self.import_statement(&mut state, i, &mut packages)?,
                ast::Statement::Type(t) => self.type_statement(&mut state, t, &mut packages)?,
                ast::Statement::Let(l) => self.let_statement(&mut state, l, &mut packages)?,
                ast::Statement::Export(e) => self.export_statement(&mut state, e, &mut packages)?,
            }
        }

        // If there's a target world in the directive, validate the composition
        // conforms to the target
        if let Some(path) = &self.0.directive.targets {
            log::debug!("validating composition targets world `{}`", path.string);
            let item = self.resolve_package_path(&mut state, path, &mut packages)?;
            match item {
                ItemKind::Type(Type::World(world)) => {
                    self.validate_target(&state, path, world)?;
                }
                _ => {
                    return Err(Error::NotWorld {
                        name: path.string.to_owned(),
                        kind: item.desc(state.graph.types()).to_owned(),
                        span: path.span,
                    });
                }
            }
        }

        Ok(Resolution {
            document: self.0,
            graph: state.graph,
            import_spans: state.import_spans,
            instantiation_spans: state.instantiation_spans,
        })
    }

    fn import_statement(
        &mut self,
        state: &mut State,
        stmt: &'a ast::ImportStatement<'a>,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> ResolutionResult<()> {
        log::debug!(
            "resolving import statement for id `{id}`",
            id = stmt.id.string
        );

        // Determine the import name to use
        let (name, span) = match &stmt.name {
            Some(name) => (name.as_str(), name.span()),
            None => match &stmt.ty {
                ast::ImportType::Package(p) => (p.string, p.span),
                ast::ImportType::Func(_) | ast::ImportType::Interface(_) => {
                    (stmt.id.string, stmt.id.span)
                }
                ast::ImportType::Ident(id) => {
                    let (item, _) = state.local_item(id)?;
                    match item.kind(&state.graph) {
                        ItemKind::Instance(id) => match &state.graph.types()[id].id {
                            Some(id) => (id.as_str(), stmt.id.span),
                            None => (stmt.id.string, stmt.id.span),
                        },
                        ItemKind::Component(id) => match &state.graph.types()[id].id {
                            Some(id) => (id.as_str(), stmt.id.span),
                            None => (stmt.id.string, stmt.id.span),
                        },
                        ItemKind::Type(_)
                        | ItemKind::Func(_)
                        | ItemKind::Module(_)
                        | ItemKind::Value(_) => (stmt.id.string, stmt.id.span),
                    }
                }
            },
        };

        let map_import_error = |state: &State, e: ImportError, span: SourceSpan| match e {
            ImportError::ImportAlreadyExists { name, node } => Error::DuplicateExternName {
                name,
                kind: ExternKind::Import,
                span,
                previous: state.import_spans[&node],
                help: if stmt.name.is_some() {
                    None
                } else {
                    Some("consider using an `as` clause to use a different name".into())
                },
            },
            ImportError::InvalidImportName { name, source } => Error::InvalidExternName {
                name,
                kind: ExternKind::Import,
                span,
                source,
            },
        };

        // Determine the kind for the item to import
        let name = name.to_string();
        let kind = match &stmt.ty {
            ast::ImportType::Package(p) => self.resolve_package_path(state, p, packages)?,
            ast::ImportType::Func(ty) => ItemKind::Func(self.func_type(
                state,
                &ty.params,
                &ty.results,
                FuncKind::Free,
                None,
            )?),
            ast::ImportType::Interface(i) => {
                ItemKind::Instance(self.inline_interface(state, i, packages)?)
            }
            ast::ImportType::Ident(id) => state.local_item(id)?.0.kind(&state.graph),
        };

        // Import the item
        log::debug!("adding import `{name}` to the graph");
        let node = state
            .graph
            .import(name, kind.promote())
            .map_err(|e| map_import_error(state, e, span))?;

        state.import_spans.insert(node, span);

        // Register the local name
        state.register_name(stmt.id, Item::Node(node))
    }

    fn type_statement(
        &mut self,
        state: &mut State,
        stmt: &'a ast::TypeStatement<'a>,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> ResolutionResult<()> {
        log::debug!("resolving type statement");

        let (id, ty) = match stmt {
            ast::TypeStatement::Interface(i) => (i.id, self.interface_decl(state, i, packages)?),
            ast::TypeStatement::World(w) => (w.id, self.world_decl(state, w, packages)?),
            ast::TypeStatement::Type(t) => (
                *t.id(),
                match t {
                    ast::TypeDecl::Variant(v) => self.variant_decl(state, v, false)?,
                    ast::TypeDecl::Record(r) => self.record_decl(state, r, false)?,
                    ast::TypeDecl::Flags(f) => self.flags_decl(state, f, false)?,
                    ast::TypeDecl::Enum(e) => self.enum_decl(state, e, false)?,
                    ast::TypeDecl::Alias(a) => self.type_alias(state, a, false)?,
                },
            ),
        };

        log::debug!("adding type definition `{id}` to the graph", id = id.string);
        let node = state
            .graph
            .define_type(id.string, ty)
            .map_err(|e| match e {
                DefineTypeError::TypeAlreadyDefined => panic!("type should not be already defined"),
                DefineTypeError::CannotDefineResource => panic!("type should not be a resource"),
                DefineTypeError::InvalidExternName { .. } => panic!("parsed an invalid type name"),
                DefineTypeError::ExportConflict { name } => Error::DeclarationConflict {
                    name,
                    span: id.span,
                    export: state.export_spans[&state.graph.get_export(id.string).unwrap()],
                },
            })?;

        state.export_spans.insert(node, id.span);
        state.register_name(id, Item::Node(node))
    }

    fn let_statement(
        &mut self,
        state: &mut State,
        stmt: &'a ast::LetStatement<'a>,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> ResolutionResult<()> {
        log::debug!("resolving let statement for id `{id}`", id = stmt.id.string);
        let item = self.expr(state, &stmt.expr, packages)?;
        state.register_name(stmt.id, item)
    }

    fn export_statement(
        &mut self,
        state: &mut State,
        stmt: &'a ast::ExportStatement<'a>,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> ResolutionResult<()> {
        log::debug!("resolving export statement");

        let item = self.expr(state, &stmt.expr, packages)?;
        match &stmt.options {
            ast::ExportOptions::None => {
                let name = self
                    .infer_export_name(state, item)
                    .ok_or(Error::ExportRequiresAs {
                        span: stmt.expr.span,
                    })?;

                self.export_item(state, item, name.to_owned(), stmt.expr.span, true)?;
            }
            ast::ExportOptions::Spread(span) => {
                let exports = match item.kind(&state.graph) {
                    ItemKind::Instance(id) => state.graph.types()[id]
                        .exports
                        .keys()
                        .cloned()
                        .collect::<Vec<_>>(),
                    kind => {
                        return Err(Error::NotAnInstance {
                            kind: kind.desc(state.graph.types()).to_string(),
                            operation: InstanceOperation::Spread,
                            span: stmt.expr.span,
                        })
                    }
                };

                let mut exported = false;
                for name in exports {
                    // Only export the item if it another item with the same name
                    // has not been already exported
                    if state.graph.get_export(&name).is_some() {
                        continue;
                    }

                    let item = self
                        .alias_export(
                            state,
                            item,
                            &name,
                            stmt.expr.span,
                            InstanceOperation::Spread,
                        )?
                        .expect("expected a matching export name");

                    self.export_item(state, item, name, *span, false)?;
                    exported = true;
                }

                if !exported {
                    return Err(Error::SpreadExportNoEffect {
                        span: stmt.expr.span,
                    });
                }
            }
            ast::ExportOptions::Rename(name) => {
                self.export_item(state, item, name.as_str().to_owned(), name.span(), false)?;
            }
        }

        Ok(())
    }

    fn infer_export_name<'b>(&self, state: &'b State, item: Item) -> Option<&'b str> {
        // If the item is an instance with an id, try the id.
        if let ItemKind::Instance(id) = item.kind(&state.graph) {
            if let Some(id) = &state.graph.types()[id].id {
                return Some(id);
            }
        }

        // If the item comes from an import or an alias, try the name associated with it
        let node = item.node();
        if let Some(name) = state.graph.get_import_name(node) {
            Some(name)
        } else if let Some((_, name)) = state.graph.get_alias_source(node) {
            Some(name)
        } else {
            None
        }
    }

    fn export_item(
        &self,
        state: &mut State,
        item: Item,
        name: String,
        span: SourceSpan,
        show_hint: bool,
    ) -> Result<(), Error> {
        if let Some((item, prev_span)) = state.root_scope().get(&name) {
            let node = &state.graph[item.node()];
            if let NodeKind::Definition = node.kind {
                return Err(Error::ExportConflict {
                    name,
                    kind: node.item_kind.desc(state.graph.types()).to_string(),
                    span,
                    definition: prev_span,
                    help: if !show_hint {
                        None
                    } else {
                        Some("consider using an `as` clause to use a different name".into())
                    },
                });
            }
        }

        let node = item.node();
        state.graph.export(item.node(), name).map_err(|e| match e {
            ExportError::ExportAlreadyExists { name, node } => Error::DuplicateExternName {
                name,
                kind: ExternKind::Export,
                span,
                previous: state.export_spans[&node],
                help: if !show_hint {
                    None
                } else {
                    Some("consider using an `as` clause to use a different name".into())
                },
            },
            wac_graph::ExportError::InvalidExportName { name, source } => {
                Error::InvalidExternName {
                    name,
                    kind: ExternKind::Export,
                    span,
                    source,
                }
            }
        })?;

        state.export_spans.insert(node, span);
        Ok(())
    }

    fn variant_decl(
        &mut self,
        state: &mut State,
        decl: &ast::VariantDecl<'a>,
        register_name: bool,
    ) -> ResolutionResult<Type> {
        log::debug!(
            "resolving variant declaration for id `{id}`",
            id = decl.id.string
        );

        let mut cases = IndexMap::new();
        for case in &decl.cases {
            let ty = case.ty.as_ref().map(|ty| Self::ty(state, ty)).transpose()?;
            if cases.insert(case.id.string.into(), ty).is_some() {
                return Err(Error::DuplicateVariantCase {
                    case: case.id.string.to_string(),
                    name: decl.id.string.to_string(),
                    span: case.id.span,
                });
            }
        }

        let ty = Type::Value(ValueType::Defined(
            state
                .graph
                .types_mut()
                .add_defined_type(DefinedType::Variant(Variant { cases })),
        ));

        if register_name {
            state.register_name(decl.id, Item::Type(ty))?;
        }

        Ok(ty)
    }

    fn record_decl(
        &mut self,
        state: &mut State,
        decl: &ast::RecordDecl<'a>,
        register_name: bool,
    ) -> ResolutionResult<Type> {
        log::debug!(
            "resolving record declaration for id `{id}`",
            id = decl.id.string
        );

        let mut fields = IndexMap::new();
        for field in &decl.fields {
            let ty = Self::ty(state, &field.ty)?;
            if fields.insert(field.id.string.into(), ty).is_some() {
                return Err(Error::DuplicateRecordField {
                    field: field.id.string.to_string(),
                    name: decl.id.string.to_string(),
                    span: field.id.span,
                });
            }
        }

        let ty = Type::Value(ValueType::Defined(
            state
                .graph
                .types_mut()
                .add_defined_type(DefinedType::Record(Record { fields })),
        ));

        if register_name {
            state.register_name(decl.id, Item::Type(ty))?;
        }

        Ok(ty)
    }

    fn flags_decl(
        &mut self,
        state: &mut State,
        decl: &ast::FlagsDecl<'a>,
        register_name: bool,
    ) -> ResolutionResult<Type> {
        log::debug!(
            "resolving flags declaration for id `{id}`",
            id = decl.id.string
        );

        let mut flags = IndexSet::new();
        for flag in &decl.flags {
            if !flags.insert(flag.id.string.into()) {
                return Err(Error::DuplicateFlag {
                    flag: flag.id.string.to_string(),
                    name: decl.id.string.to_string(),
                    span: flag.id.span,
                });
            }
        }

        let ty = Type::Value(ValueType::Defined(
            state
                .graph
                .types_mut()
                .add_defined_type(DefinedType::Flags(Flags(flags))),
        ));

        if register_name {
            state.register_name(decl.id, Item::Type(ty))?;
        }

        Ok(ty)
    }

    fn enum_decl(
        &mut self,
        state: &mut State,
        decl: &ast::EnumDecl<'a>,
        register_name: bool,
    ) -> ResolutionResult<Type> {
        log::debug!(
            "resolving enum declaration for id `{id}`",
            id = decl.id.string
        );

        let mut cases = IndexSet::new();
        for case in &decl.cases {
            if !cases.insert(case.id.string.to_owned()) {
                return Err(Error::DuplicateEnumCase {
                    case: case.id.string.to_string(),
                    name: decl.id.string.to_string(),
                    span: case.id.span,
                });
            }
        }

        let ty = Type::Value(ValueType::Defined(
            state
                .graph
                .types_mut()
                .add_defined_type(DefinedType::Enum(Enum(cases))),
        ));

        if register_name {
            state.register_name(decl.id, Item::Type(ty))?;
        }

        Ok(ty)
    }

    fn type_alias(
        &mut self,
        state: &mut State,
        alias: &ast::TypeAlias<'a>,
        register_name: bool,
    ) -> ResolutionResult<Type> {
        log::debug!("resolving type alias for id `{id}`", id = alias.id.string);

        let ty = match &alias.kind {
            ast::TypeAliasKind::Func(f) => {
                Type::Func(self.func_type(state, &f.params, &f.results, FuncKind::Free, None)?)
            }
            ast::TypeAliasKind::Type(ty) => match ty {
                ast::Type::Ident(id) => {
                    let (item, _) = state.local_item(id)?;
                    match item.kind(&state.graph) {
                        ItemKind::Type(Type::Resource(id)) => {
                            let owner = state.graph.types()[id].alias.and_then(|a| a.owner);
                            Type::Resource(state.graph.types_mut().add_resource(Resource {
                                name: alias.id.string.to_owned(),
                                alias: Some(ResourceAlias { owner, source: id }),
                            }))
                        }
                        ItemKind::Type(Type::Value(ty)) => Type::Value(ValueType::Defined(
                            state
                                .graph
                                .types_mut()
                                .add_defined_type(DefinedType::Alias(ty)),
                        )),
                        ItemKind::Type(Type::Func(id)) | ItemKind::Func(id) => {
                            let ty = state.graph.types()[id].clone();
                            Type::Func(state.graph.types_mut().add_func_type(ty))
                        }
                        kind => {
                            return Err(Error::InvalidAliasType {
                                name: id.string.to_string(),
                                kind: kind.desc(state.graph.types()).to_string(),
                                span: id.span,
                            });
                        }
                    }
                }
                _ => {
                    let ty = Self::ty(state, ty)?;
                    Type::Value(ValueType::Defined(
                        state
                            .graph
                            .types_mut()
                            .add_defined_type(DefinedType::Alias(ty)),
                    ))
                }
            },
        };

        if register_name {
            state.register_name(alias.id, Item::Type(ty))?;
        }

        Ok(ty)
    }

    fn func_type_ref(
        &mut self,
        state: &mut State,
        r: &ast::FuncTypeRef<'a>,
        kind: FuncKind,
    ) -> ResolutionResult<FuncTypeId> {
        match r {
            ast::FuncTypeRef::Func(ty) => {
                self.func_type(state, &ty.params, &ty.results, kind, None)
            }
            ast::FuncTypeRef::Ident(id) => {
                let (item, _) = state.local_item(id)?;
                match item.kind(&state.graph) {
                    ItemKind::Type(Type::Func(id)) | ItemKind::Func(id) => Ok(id),
                    kind => Err(Error::NotFuncType {
                        name: id.string.to_string(),
                        kind: kind.desc(state.graph.types()).to_string(),
                        span: id.span,
                    }),
                }
            }
        }
    }

    fn ty(state: &mut State, ty: &ast::Type<'a>) -> ResolutionResult<ValueType> {
        match ty {
            ast::Type::U8(_) => Ok(ValueType::Primitive(PrimitiveType::U8)),
            ast::Type::S8(_) => Ok(ValueType::Primitive(PrimitiveType::S8)),
            ast::Type::U16(_) => Ok(ValueType::Primitive(PrimitiveType::U16)),
            ast::Type::S16(_) => Ok(ValueType::Primitive(PrimitiveType::S16)),
            ast::Type::U32(_) => Ok(ValueType::Primitive(PrimitiveType::U32)),
            ast::Type::S32(_) => Ok(ValueType::Primitive(PrimitiveType::S32)),
            ast::Type::U64(_) => Ok(ValueType::Primitive(PrimitiveType::U64)),
            ast::Type::S64(_) => Ok(ValueType::Primitive(PrimitiveType::S64)),
            ast::Type::F32(_) => Ok(ValueType::Primitive(PrimitiveType::F32)),
            ast::Type::F64(_) => Ok(ValueType::Primitive(PrimitiveType::F64)),
            ast::Type::Char(_) => Ok(ValueType::Primitive(PrimitiveType::Char)),
            ast::Type::Bool(_) => Ok(ValueType::Primitive(PrimitiveType::Bool)),
            ast::Type::String(_) => Ok(ValueType::Primitive(PrimitiveType::String)),
            ast::Type::Tuple(v, _) => {
                let tuple = DefinedType::Tuple(
                    v.iter()
                        .map(|ty| Self::ty(state, ty))
                        .collect::<ResolutionResult<_>>()?,
                );

                Ok(ValueType::Defined(
                    state.graph.types_mut().add_defined_type(tuple),
                ))
            }
            ast::Type::List(ty, _) => {
                let ty = Self::ty(state, ty)?;
                Ok(ValueType::Defined(
                    state
                        .graph
                        .types_mut()
                        .add_defined_type(DefinedType::List(ty)),
                ))
            }
            ast::Type::Option(ty, _) => {
                let ty = Self::ty(state, ty)?;
                Ok(ValueType::Defined(
                    state
                        .graph
                        .types_mut()
                        .add_defined_type(DefinedType::Option(ty)),
                ))
            }
            ast::Type::Result { ok, err, .. } => {
                let ok = ok.as_ref().map(|t| Self::ty(state, t)).transpose()?;
                let err = err.as_ref().map(|t| Self::ty(state, t)).transpose()?;
                Ok(ValueType::Defined(
                    state
                        .graph
                        .types_mut()
                        .add_defined_type(DefinedType::Result { ok, err }),
                ))
            }
            ast::Type::Borrow(id, _) => {
                let (item, _) = state.local_item(id)?;
                let kind = item.kind(&state.graph);
                if let ItemKind::Type(Type::Resource(id)) = kind {
                    return Ok(ValueType::Borrow(id));
                }

                Err(Error::NotResourceType {
                    name: id.string.to_string(),
                    kind: kind.desc(state.graph.types()).to_string(),
                    span: id.span,
                })
            }
            ast::Type::Ident(id) => {
                let (item, _) = state.local_item(id)?;
                let kind = item.kind(&state.graph);
                match kind {
                    ItemKind::Type(Type::Resource(id)) => Ok(ValueType::Own(id)),
                    ItemKind::Type(Type::Value(ty)) => Ok(ty),
                    _ => Err(Error::NotValueType {
                        name: id.string.to_string(),
                        kind: kind.desc(state.graph.types()).to_string(),
                        span: id.span,
                    }),
                }
            }
        }
    }

    fn id(&self, name: &str) -> String {
        format!(
            "{pkg}/{name}{version}",
            pkg = self.0.directive.package.name,
            version = if let Some(version) = &self.0.directive.package.version {
                format!("@{version}")
            } else {
                String::new()
            }
        )
    }

    fn interface_decl(
        &mut self,
        state: &mut State,
        decl: &'a ast::InterfaceDecl<'a>,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> ResolutionResult<Type> {
        log::debug!(
            "resolving interface declaration for id `{id}`",
            id = decl.id.string
        );
        state.push_scope();

        let mut ty = Interface {
            id: Some(self.id(decl.id.string)),
            uses: Default::default(),
            exports: Default::default(),
        };

        self.interface_items(state, Some(decl.id.string), &decl.items, packages, &mut ty)?;

        state.pop_scope();

        Ok(Type::Interface(state.graph.types_mut().add_interface(ty)))
    }

    fn world_decl(
        &mut self,
        state: &mut State,
        decl: &'a ast::WorldDecl<'a>,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> ResolutionResult<Type> {
        log::debug!(
            "resolving world declaration for id `{id}`",
            id = decl.id.string
        );
        state.push_scope();

        let mut ty = World {
            id: Some(self.id(decl.id.string)),
            uses: Default::default(),
            imports: Default::default(),
            exports: Default::default(),
        };

        self.world_items(state, decl.id.string, &decl.items, packages, &mut ty)?;

        state.pop_scope();

        Ok(Type::World(state.graph.types_mut().add_world(ty)))
    }

    fn world_items(
        &mut self,
        state: &mut State,
        world: &'a str,
        items: &'a [ast::WorldItem<'a>],
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
        ty: &mut World,
    ) -> ResolutionResult<()> {
        let mut includes = Vec::new();
        for item in items {
            match item {
                ast::WorldItem::Use(u) => {
                    self.use_type(state, u, &mut ty.uses, &mut ty.imports, packages, true)?
                }
                ast::WorldItem::Type(decl) => {
                    self.item_type_decl(state, decl, &mut ty.imports)?;
                }
                ast::WorldItem::Import(i) => {
                    self.world_item_path(state, &i.path, ExternKind::Import, world, packages, ty)?
                }
                ast::WorldItem::Export(e) => {
                    self.world_item_path(state, &e.path, ExternKind::Export, world, packages, ty)?
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
            self.world_include(state, i, world, packages, ty)?;
        }

        Ok(())
    }

    fn world_item_path(
        &mut self,
        state: &mut State,
        path: &'a ast::WorldItemPath<'a>,
        kind: ExternKind,
        world: &'a str,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
        ty: &mut World,
    ) -> ResolutionResult<()> {
        let (k, v) = match path {
            ast::WorldItemPath::Named(named) => {
                check_name(named.id.string, named.id.span, ty, world, kind)?;

                (
                    named.id.string.into(),
                    match &named.ty {
                        ast::ExternType::Ident(id) => {
                            let (item, _) = state.local_or_root_item(id)?;
                            match item.kind(&state.graph) {
                                ItemKind::Type(Type::Interface(id)) => ItemKind::Instance(id),
                                ItemKind::Type(Type::Func(id)) => ItemKind::Func(id),
                                kind => {
                                    return Err(Error::NotFuncOrInterface {
                                        name: id.string.to_owned(),
                                        kind: kind.desc(state.graph.types()).to_owned(),
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
                            None,
                        )?),
                        ast::ExternType::Interface(i) => {
                            ItemKind::Instance(self.inline_interface(state, i, packages)?)
                        }
                    },
                )
            }
            ast::WorldItemPath::Ident(id) => {
                let (item, _) = state.root_item(id)?;
                match item.kind(&state.graph) {
                    ItemKind::Type(Type::Interface(iface_ty_id)) => {
                        let iface_id = state.graph.types()[iface_ty_id]
                            .id
                            .as_ref()
                            .expect("expected an interface id");
                        check_name(iface_id, id.span, ty, world, kind)?;
                        (iface_id.clone(), ItemKind::Instance(iface_ty_id))
                    }
                    kind => {
                        return Err(Error::NotInterface {
                            name: id.string.to_owned(),
                            kind: kind.desc(state.graph.types()).to_owned(),
                            span: id.span,
                        });
                    }
                }
            }

            ast::WorldItemPath::Package(p) => {
                match self.resolve_package_path(state, p, packages)? {
                    ItemKind::Type(Type::Interface(id)) => {
                        let name = state.graph.types()[id]
                            .id
                            .as_ref()
                            .expect("expected an interface id");
                        check_name(name, p.span, ty, world, kind)?;
                        (name.clone(), ItemKind::Instance(id))
                    }
                    kind => {
                        return Err(Error::NotInterface {
                            name: p.string.to_owned(),
                            kind: kind.desc(state.graph.types()).to_owned(),
                            span: p.span,
                        });
                    }
                }
            }
        };

        if kind == ExternKind::Import {
            ty.imports.insert(k, v);
        } else {
            ty.exports.insert(k, v);
        }

        return Ok(());

        fn check_name(
            name: &str,
            span: SourceSpan,
            ty: &World,
            world: &str,
            kind: ExternKind,
        ) -> ResolutionResult<()> {
            let exists: bool = if kind == ExternKind::Import {
                ty.imports.contains_key(name)
            } else {
                ty.exports.contains_key(name)
            };

            if exists {
                return Err(Error::DuplicateWorldItem {
                    kind,
                    name: name.to_owned(),
                    world: world.to_owned(),
                    span,
                });
            }

            Ok(())
        }
    }

    fn world_include(
        &mut self,
        state: &mut State,
        include: &'a ast::WorldInclude<'a>,
        world: &'a str,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
        ty: &mut World,
    ) -> ResolutionResult<()> {
        log::debug!("resolving include of world `{world}`");
        let mut replacements = HashMap::new();
        for item in &include.with {
            let prev = replacements.insert(item.from.string, item);
            if prev.is_some() {
                return Err(Error::DuplicateWorldIncludeName {
                    name: item.from.string.to_owned(),
                    span: item.from.span,
                });
            }
        }

        let id = match &include.world {
            ast::WorldRef::Ident(id) => {
                let (item, _) = state.root_item(id)?;
                match item.kind(&state.graph) {
                    ItemKind::Type(Type::World(id)) | ItemKind::Component(id) => id,
                    kind => {
                        return Err(Error::NotWorld {
                            name: id.string.to_owned(),
                            kind: kind.desc(state.graph.types()).to_owned(),
                            span: id.span,
                        });
                    }
                }
            }
            ast::WorldRef::Package(path) => {
                match self.resolve_package_path(state, path, packages)? {
                    ItemKind::Type(Type::World(id)) | ItemKind::Component(id) => id,
                    kind => {
                        return Err(Error::NotWorld {
                            name: path.string.to_owned(),
                            kind: kind.desc(state.graph.types()).to_owned(),
                            span: path.span,
                        });
                    }
                }
            }
        };

        let other = &state.graph.types()[id];
        for (name, item) in &other.imports {
            let name = replace_name(
                include,
                world,
                ty,
                name,
                ExternKind::Import,
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
                ExternKind::Export,
                &mut replacements,
            )?;
            ty.exports.entry(name).or_insert(*item);
        }

        if let Some(missing) = replacements.values().next() {
            return Err(Error::MissingWorldInclude {
                world: include.world.name().to_owned(),
                name: missing.from.string.to_owned(),
                span: missing.from.span,
            });
        }

        return Ok(());

        fn replace_name<'a>(
            include: &ast::WorldInclude<'a>,
            world: &'a str,
            ty: &mut World,
            name: &str,
            kind: ExternKind,
            replacements: &mut HashMap<&str, &ast::WorldIncludeItem<'a>>,
        ) -> ResolutionResult<String> {
            // Check for a id, which doesn't get replaced.
            if name.contains(':') {
                return Ok(name.to_owned());
            }

            let (name, span) = replacements
                .remove(name)
                .map(|i| (i.to.string, i.to.span))
                .unwrap_or_else(|| (name, include.world.span()));

            let exists = if kind == ExternKind::Import {
                ty.imports.contains_key(name)
            } else {
                ty.exports.contains_key(name)
            };

            if exists {
                return Err(Error::WorldIncludeConflict {
                    kind,
                    name: name.to_owned(),
                    from: include.world.name().to_owned(),
                    to: world.to_owned(),
                    span,
                    help: if !include.with.is_empty() {
                        None
                    } else {
                        Some("consider using a `with` clause to use a different name".into())
                    },
                });
            }

            Ok(name.to_owned())
        }
    }

    fn inline_interface(
        &mut self,
        state: &mut State,
        iface: &'a ast::InlineInterface<'a>,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> ResolutionResult<InterfaceId> {
        log::debug!("resolving inline interface");

        state.push_scope();

        let mut ty = Interface {
            id: None,
            uses: Default::default(),
            exports: Default::default(),
        };

        self.interface_items(state, None, &iface.items, packages, &mut ty)?;

        state.pop_scope();

        Ok(state.graph.types_mut().add_interface(ty))
    }

    fn interface_items(
        &mut self,
        state: &mut State,
        name: Option<&'a str>,
        items: &'a [ast::InterfaceItem<'a>],
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
        ty: &mut Interface,
    ) -> ResolutionResult<()> {
        for item in items {
            match item {
                ast::InterfaceItem::Use(u) => {
                    self.use_type(state, u, &mut ty.uses, &mut ty.exports, packages, false)?
                }
                ast::InterfaceItem::Type(decl) => {
                    self.item_type_decl(state, decl, &mut ty.exports)?;
                }
                ast::InterfaceItem::Export(e) => {
                    let kind = ItemKind::Func(self.func_type_ref(state, &e.ty, FuncKind::Free)?);
                    if ty.exports.insert(e.id.string.into(), kind).is_some() {
                        return Err(Error::DuplicateInterfaceExport {
                            name: e.id.string.to_owned(),
                            interface_name: name.map(ToOwned::to_owned),
                            span: e.id.span,
                        });
                    }
                }
            }
        }

        Ok(())
    }

    fn use_type(
        &mut self,
        state: &mut State,
        use_type: &'a ast::Use<'a>,
        uses: &mut IndexMap<String, UsedType>,
        externs: &mut IndexMap<String, ItemKind>,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
        in_world: bool,
    ) -> ResolutionResult<()> {
        let (interface, name) = match &use_type.path {
            ast::UsePath::Package(path) => {
                match self.resolve_package_path(state, path, packages)? {
                    ItemKind::Type(Type::Interface(id)) => (id, path.string),
                    kind => {
                        return Err(Error::NotInterface {
                            name: path.string.to_owned(),
                            kind: kind.desc(state.graph.types()).to_owned(),
                            span: path.span,
                        });
                    }
                }
            }
            ast::UsePath::Ident(id) => {
                let (item, _) = state.root_item(id)?;
                let kind = item.kind(&state.graph);
                match kind {
                    ItemKind::Type(Type::Interface(iface_ty_id)) => (iface_ty_id, id.string),
                    _ => {
                        return Err(Error::NotInterface {
                            name: id.string.to_owned(),
                            kind: kind.desc(state.graph.types()).to_owned(),
                            span: id.span,
                        });
                    }
                }
            }
        };

        for item in &use_type.items {
            let ident = item.as_id.unwrap_or(item.id);
            let kind = state.graph.types()[interface]
                .exports
                .get(item.id.string)
                .ok_or(Error::UndefinedInterfaceType {
                    name: item.id.string.to_string(),
                    interface_name: name.to_string(),
                    span: item.id.span,
                })?;

            match kind {
                ItemKind::Type(ty @ Type::Resource(_)) | ItemKind::Type(ty @ Type::Value(_)) => {
                    if externs.contains_key(ident.string) {
                        return Err(Error::UseConflict {
                            name: ident.string.to_string(),
                            kind: if in_world {
                                ExternKind::Import
                            } else {
                                ExternKind::Export
                            },
                            span: ident.span,
                            help: if item.as_id.is_some() {
                                None
                            } else {
                                Some("consider using an `as` clause to use a different name".into())
                            },
                        });
                    }

                    uses.insert(
                        ident.string.into(),
                        UsedType {
                            interface,
                            name: item.as_id.map(|_| item.id.string.to_string()),
                        },
                    );
                    externs.insert(ident.string.into(), *kind);
                    state.register_name(ident, Item::Use(*ty))?;
                }
                _ => {
                    return Err(Error::NotInterfaceValueType {
                        name: item.id.string.to_string(),
                        kind: kind.desc(state.graph.types()).to_string(),
                        interface_name: name.to_string(),
                        span: item.id.span,
                    });
                }
            }
        }

        Ok(())
    }

    fn item_type_decl(
        &mut self,
        state: &mut State,
        decl: &'a ast::ItemTypeDecl,
        externs: &mut IndexMap<String, ItemKind>,
    ) -> ResolutionResult<()> {
        let (insert, ty) = match decl {
            ast::ItemTypeDecl::Resource(r) => (false, self.resource_decl(state, r, externs)?),
            ast::ItemTypeDecl::Variant(v) => (true, self.variant_decl(state, v, true)?),
            ast::ItemTypeDecl::Record(r) => (true, self.record_decl(state, r, true)?),
            ast::ItemTypeDecl::Flags(f) => (true, self.flags_decl(state, f, true)?),
            ast::ItemTypeDecl::Enum(e) => (true, self.enum_decl(state, e, true)?),
            ast::ItemTypeDecl::Alias(a) => (true, self.type_alias(state, a, true)?),
        };

        if insert {
            let prev = externs.insert(decl.id().string.into(), ItemKind::Type(ty));
            assert!(prev.is_none(), "duplicate type in scope");
        }

        Ok(())
    }

    fn resource_decl(
        &mut self,
        state: &mut State,
        decl: &ast::ResourceDecl<'a>,
        externs: &mut IndexMap<String, ItemKind>,
    ) -> ResolutionResult<Type> {
        log::debug!(
            "resolving resource declaration for id `{id}`",
            id = decl.id.string
        );

        // Define the resource before resolving the methods
        let id = state.graph.types_mut().add_resource(Resource {
            name: decl.id.string.to_owned(),
            alias: None,
        });

        let ty = Type::Resource(id);
        state.register_name(decl.id, Item::Type(ty))?;

        // We must add the resource to the externs before any methods
        let prev = externs.insert(decl.id.string.into(), ItemKind::Type(ty));
        assert!(prev.is_none());

        let mut names = HashSet::new();
        for method in &decl.methods {
            let (name, ty) = match method {
                ast::ResourceMethod::Constructor(ast::Constructor { span, params, .. }) => {
                    if !names.insert("") {
                        return Err(Error::DuplicateResourceConstructor {
                            resource: decl.id.string.to_string(),
                            span: *span,
                        });
                    }

                    (
                        method_extern_name(decl.id.string, "", FuncKind::Constructor),
                        self.func_type(
                            state,
                            params,
                            &ast::ResultList::Empty,
                            FuncKind::Constructor,
                            Some(id),
                        )?,
                    )
                }
                ast::ResourceMethod::Method(ast::Method {
                    id: method_id,
                    is_static,
                    ty,
                    ..
                }) => {
                    let kind = if *is_static {
                        FuncKind::Static
                    } else {
                        FuncKind::Method
                    };

                    if !names.insert(method_id.string) {
                        return Err(Error::DuplicateResourceMethod {
                            name: method_id.string.to_string(),
                            resource: decl.id.string.to_string(),
                            span: method_id.span,
                        });
                    }

                    (
                        method_extern_name(decl.id.string, method_id.string, kind),
                        self.func_type(state, &ty.params, &ty.results, kind, Some(id))?,
                    )
                }
            };

            let prev = externs.insert(name, ItemKind::Func(ty));
            assert!(prev.is_none());
        }

        Ok(ty)
    }

    fn func_type(
        &mut self,
        state: &mut State,
        func_params: &[ast::NamedType<'a>],
        func_results: &ast::ResultList<'a>,
        kind: FuncKind,
        resource: Option<ResourceId>,
    ) -> ResolutionResult<FuncTypeId> {
        let mut params = IndexMap::new();

        if kind == FuncKind::Method {
            params.insert("self".into(), ValueType::Borrow(resource.unwrap()));
        }

        for param in func_params {
            if params
                .insert(param.id.string.into(), Self::ty(state, &param.ty)?)
                .is_some()
            {
                return Err(Error::DuplicateParameter {
                    name: param.id.string.to_string(),
                    kind,
                    span: param.id.span,
                });
            }
        }

        let results = match func_results {
            ast::ResultList::Empty => {
                if kind == FuncKind::Constructor {
                    Some(FuncResult::Scalar(ValueType::Own(resource.unwrap())))
                } else {
                    None
                }
            }
            ast::ResultList::Named(results) => {
                let mut list = IndexMap::new();
                for result in results {
                    let value_type = Self::ty(state, &result.ty)?;
                    if value_type.contains_borrow(state.graph.types()) {
                        return Err(Error::BorrowInResult {
                            span: result.ty.span(),
                        });
                    }

                    if list
                        .insert(result.id.string.to_owned(), value_type)
                        .is_some()
                    {
                        return Err(Error::DuplicateResult {
                            name: result.id.string.to_string(),
                            kind,
                            span: result.id.span,
                        });
                    }
                }
                Some(FuncResult::List(list))
            }
            ast::ResultList::Scalar(ty) => {
                let value_type = Self::ty(state, ty)?;
                if value_type.contains_borrow(state.graph.types()) {
                    return Err(Error::BorrowInResult { span: ty.span() });
                }
                Some(FuncResult::Scalar(value_type))
            }
        };

        Ok(state
            .graph
            .types_mut()
            .add_func_type(FuncType { params, results }))
    }

    fn expr(
        &mut self,
        state: &mut State,
        expr: &'a ast::Expr<'a>,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> ResolutionResult<Item> {
        let mut item = self.primary_expr(state, &expr.primary, packages)?;

        let mut parent_span = expr.primary.span();
        for expr in &expr.postfix {
            item = self.postfix_expr(state, item, expr, parent_span)?;
            parent_span = expr.span();
        }

        Ok(item)
    }

    fn primary_expr(
        &mut self,
        state: &mut State,
        expr: &'a ast::PrimaryExpr<'a>,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> ResolutionResult<Item> {
        match expr {
            ast::PrimaryExpr::New(e) => self.new_expr(state, e, packages),
            ast::PrimaryExpr::Nested(e) => self.expr(state, &e.inner, packages),
            ast::PrimaryExpr::Ident(i) => Ok(state.local_item(i)?.0),
        }
    }

    fn new_expr(
        &mut self,
        state: &mut State,
        expr: &'a ast::NewExpr<'a>,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> ResolutionResult<Item> {
        log::debug!(
            "resolving new expression for package `{pkg}`",
            pkg = BorrowedPackageKey::from_name_and_version(
                expr.package.name,
                expr.package.version.as_ref()
            )
        );

        if expr.package.name == self.0.directive.package.name {
            return Err(Error::UnknownPackage {
                name: expr.package.name.to_string(),
                span: expr.package.span,
            });
        }

        let pkg = self.resolve_package(
            state,
            expr.package.name,
            expr.package.version.as_ref(),
            expr.package.span,
            packages,
        )?;
        let ty = state.graph[pkg].ty();
        let expected = state.graph.types()[ty]
            .imports
            .keys()
            .cloned()
            .collect::<IndexSet<_>>();
        let mut require_all = true;

        let mut arguments: IndexMap<String, (Item, SourceSpan)> = Default::default();
        for (i, arg) in expr.arguments.iter().enumerate() {
            let (name, item, span) = match arg {
                ast::InstantiationArgument::Inferred(id) => {
                    self.inferred_instantiation_arg(state, id, ty)?
                }
                ast::InstantiationArgument::Spread(_) => {
                    // Spread arguments will be processed after all other arguments
                    continue;
                }
                ast::InstantiationArgument::Named(arg) => {
                    self.named_instantiation_arg(state, arg, ty, packages)?
                }
                ast::InstantiationArgument::Fill(span) => {
                    if i != (expr.arguments.len() - 1) {
                        return Err(Error::FillArgumentNotLast { span: *span });
                    }

                    require_all = false;
                    continue;
                }
            };

            let prev = arguments.insert(name.clone(), (item, span));
            if prev.is_some() {
                return Err(Error::DuplicateInstantiationArg { name, span });
            }
        }

        // Process the spread arguments
        for arg in &expr.arguments {
            if let ast::InstantiationArgument::Spread(id) = arg {
                self.spread_instantiation_arg(state, id, &expected, &mut arguments)?;
            }
        }

        // Create the instantiation node
        log::debug!(
            "adding instantiation for package `{pkg}` to the graph",
            pkg = BorrowedPackageKey::from_name_and_version(
                expr.package.name,
                expr.package.version.as_ref()
            )
        );
        let instantiation = state.graph.instantiate(pkg);
        let prev = state
            .instantiation_spans
            .insert(instantiation, expr.package.span);
        assert!(prev.is_none());

        // Set the arguments on the instantiation
        for (name, (argument, span)) in &arguments {
            log::debug!("adding argument edge `{name}`");
            state
                .graph
                .set_instantiation_argument(instantiation, name, argument.node())
                .map_err(|e| match e {
                    InstantiationArgumentError::NodeIsNotAnInstantiation { .. } => {
                        panic!("node should be an instantiation")
                    }
                    InstantiationArgumentError::ArgumentAlreadyPassed { .. } => {
                        panic!("argument should not already be passed")
                    }
                    InstantiationArgumentError::InvalidArgumentName {
                        node: _,
                        name,
                        package,
                    } => Error::MissingComponentImport {
                        package,
                        import: name,
                        span: *span,
                    },
                    InstantiationArgumentError::ArgumentTypeMismatch { name, source } => {
                        Error::MismatchedInstantiationArg {
                            name,
                            span: *span,
                            source,
                        }
                    }
                })?;
        }

        // If `...` was not present in the argument list, error if there are
        // any missing arguments; implicit arguments will be added during encoding
        if require_all {
            let world = &state.graph.types()[ty];
            if let Some((name, _)) = world
                .imports
                .iter()
                .find(|(n, _)| !arguments.contains_key(n.as_str()))
            {
                return Err(Error::MissingInstantiationArg {
                    name: name.clone(),
                    package: expr.package.string.to_string(),
                    span: expr.package.span,
                });
            }
        }

        Ok(Item::Node(instantiation))
    }

    fn find_matching_interface_name<'b>(
        name: &str,
        externs: &'b IndexMap<String, ItemKind>,
    ) -> Option<&'b str> {
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

    fn named_instantiation_arg(
        &mut self,
        state: &mut State,
        arg: &'a ast::NamedInstantiationArgument<'a>,
        world: WorldId,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> ResolutionResult<(String, Item, SourceSpan)> {
        let item = self.expr(state, &arg.expr, packages)?;

        let name = match &arg.name {
            ast::InstantiationArgumentName::Ident(ident) => Self::find_matching_interface_name(
                ident.string,
                &state.graph.types()[world].imports,
            )
            .unwrap_or(ident.string),
            ast::InstantiationArgumentName::String(name) => name.value,
        };

        Ok((name.to_owned(), item, arg.name.span()))
    }

    fn inferred_instantiation_arg(
        &mut self,
        state: &mut State,
        ident: &ast::Ident<'a>,
        world: WorldId,
    ) -> ResolutionResult<(String, Item, SourceSpan)> {
        let (item, _) = state.local_item(ident)?;
        let world = &state.graph.types()[world];
        let kind = item.kind(&state.graph);

        // If the item is an instance with an id, try the id.
        if let ItemKind::Instance(id) = kind {
            if let Some(id) = &state.graph.types()[id].id {
                if world.imports.contains_key(id.as_str()) {
                    return Ok((id.clone(), item, ident.span));
                }
            }
        }

        // If the item comes from an import or an alias, try the name associated with it
        let node = item.node();
        if let Some(name) = state.graph.get_import_name(node) {
            if world.imports.contains_key(name) {
                return Ok((name.to_string(), item, ident.span));
            }
        } else if let Some((_, name)) = state.graph.get_alias_source(node) {
            if world.imports.contains_key(name) {
                return Ok((name.to_string(), item, ident.span));
            }
        }

        // Fall back to searching for a matching interface name, provided it is not ambiguous
        // For example, match `foo:bar/baz` if `baz` is the identifier and the only match
        if let Some(name) = Self::find_matching_interface_name(ident.string, &world.imports) {
            return Ok((name.to_owned(), item, ident.span));
        }

        // Finally default to the id itself
        Ok((ident.string.to_owned(), item, ident.span))
    }

    fn spread_instantiation_arg(
        &mut self,
        state: &mut State,
        id: &ast::Ident,
        expected: &IndexSet<String>,
        arguments: &mut IndexMap<String, (Item, SourceSpan)>,
    ) -> ResolutionResult<()> {
        let item = state.local_item(id)?.0;

        // The item must be an instance for a spread
        match item.kind(&state.graph) {
            ItemKind::Instance(_) => {}
            kind => {
                return Err(Error::NotAnInstance {
                    kind: kind.desc(state.graph.types()).to_string(),
                    operation: InstanceOperation::Spread,
                    span: id.span,
                })
            }
        }

        let mut spread = false;
        for name in expected {
            // Check if the argument was already provided
            if arguments.contains_key(name) {
                continue;
            }

            // Alias a matching export of the instance
            if let Some(aliased) =
                self.alias_export(state, item, name, id.span, InstanceOperation::Spread)?
            {
                spread = true;
                arguments.insert(name.clone(), (aliased, id.span));
            }
        }

        if !spread {
            return Err(Error::SpreadInstantiationNoMatch { span: id.span });
        }

        Ok(())
    }

    fn postfix_expr(
        &mut self,
        state: &mut State,
        item: Item,
        expr: &ast::PostfixExpr,
        parent_span: SourceSpan,
    ) -> ResolutionResult<Item> {
        match expr {
            ast::PostfixExpr::Access(expr) => {
                let exports = match item.kind(&state.graph) {
                    ItemKind::Instance(id) => &state.graph.types()[id].exports,
                    kind => {
                        return Err(Error::NotAnInstance {
                            kind: kind.desc(state.graph.types()).to_string(),
                            operation: InstanceOperation::Access,
                            span: parent_span,
                        })
                    }
                };

                let name = Self::find_matching_interface_name(expr.id.string, exports)
                    .unwrap_or(expr.id.string)
                    .to_string();

                self.alias_export(state, item, &name, parent_span, InstanceOperation::Access)?
                    .ok_or_else(|| Error::MissingInstanceExport {
                        name,
                        span: expr.span,
                    })
            }
            ast::PostfixExpr::NamedAccess(expr) => self
                .alias_export(
                    state,
                    item,
                    expr.string.value,
                    parent_span,
                    InstanceOperation::Access,
                )?
                .ok_or_else(|| Error::MissingInstanceExport {
                    name: expr.string.value.to_owned(),
                    span: expr.span,
                }),
        }
    }

    fn alias_export(
        &self,
        state: &mut State,
        item: Item,
        name: &str,
        span: SourceSpan,
        operation: InstanceOperation,
    ) -> ResolutionResult<Option<Item>> {
        let exports = match item.kind(&state.graph) {
            ItemKind::Instance(id) => &state.graph.types()[id].exports,
            kind => {
                return Err(Error::NotAnInstance {
                    kind: kind.desc(state.graph.types()).to_string(),
                    operation,
                    span,
                })
            }
        };

        if exports.get(name).is_none() {
            return Ok(None);
        }

        let node = state
            .graph
            .alias_instance_export(item.node(), name)
            .expect("alias should be created");

        // Insert the span if the node isn't new
        Ok(Some(Item::Node(node)))
    }

    fn resolve_package_path(
        &mut self,
        state: &mut State,
        path: &'a ast::PackagePath<'a>,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> ResolutionResult<ItemKind> {
        log::debug!("resolving package export `{path}`", path = path.string);

        // Check for reference to local item
        if path.name == self.0.directive.package.name {
            return self.resolve_local_path(state, path);
        }

        let id = self.resolve_package(
            state,
            path.name,
            path.version.as_ref(),
            path.package_name_span(),
            packages,
        )?;

        let package = &state.graph[id];
        let mut current = 0;
        let mut parent_ty = None;
        let mut found = None;
        for (i, (segment, _)) in path.segment_spans().enumerate() {
            current = i;

            // Look up the first segment in the package definitions
            if i == 0 {
                found = package.definitions().get(segment).copied();
                continue;
            }

            // Otherwise, project into the parent based on the current segment
            let export = match found.unwrap() {
                // The parent is an interface or instance
                ItemKind::Type(Type::Interface(id)) | ItemKind::Instance(id) => {
                    state.graph.types()[id].exports.get(segment).copied()
                }
                // The parent is a world or component or component instantiation
                ItemKind::Type(Type::World(id)) | ItemKind::Component(id) => {
                    state.graph.types()[id].exports.get(segment).copied()
                }
                _ => None,
            };

            parent_ty = found.map(|kind| kind.desc(state.graph.types()));
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
                        package: path.name.to_string(),
                        export: segment.to_string(),
                        kind: parent_ty.map(ToOwned::to_owned),
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

    fn resolve_local_path(
        &self,
        state: &State,
        path: &ast::PackagePath<'a>,
    ) -> ResolutionResult<ItemKind> {
        log::debug!("resolving local path `{path}`", path = path.string);

        let mut segments = path.segment_spans();
        let (segment, span) = segments.next().unwrap();
        let (item, _) = state.root_item(&ast::Ident {
            string: segment,
            span,
        })?;

        let mut current = segment;
        let mut kind = item.kind(&state.graph);
        for (segment, span) in segments {
            let exports = match kind {
                ItemKind::Type(Type::Interface(id)) | ItemKind::Instance(id) => {
                    &state.graph.types()[id].exports
                }
                ItemKind::Type(Type::World(id)) | ItemKind::Component(id) => {
                    &state.graph.types()[id].exports
                }
                _ => {
                    return Err(Error::PackagePathMissingExport {
                        name: current.to_string(),
                        kind: kind.desc(state.graph.types()).to_string(),
                        export: segment.to_string(),
                        span,
                    });
                }
            };

            kind =
                exports
                    .get(segment)
                    .copied()
                    .ok_or_else(|| Error::PackagePathMissingExport {
                        name: current.to_string(),
                        kind: kind.desc(state.graph.types()).to_string(),
                        export: segment.to_string(),
                        span,
                    })?;

            current = segment;
        }

        Ok(kind)
    }

    fn resolve_package(
        &mut self,
        state: &mut State,
        name: &'a str,
        version: Option<&'a Version>,
        span: SourceSpan,
        packages: &mut IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> ResolutionResult<PackageId> {
        match state.graph.get_package_by_name(name, version) {
            Some((id, _)) => Ok(id),
            None => {
                let bytes = packages
                    .swap_remove(&BorrowedPackageKey::from_name_and_version(name, version))
                    .ok_or_else(|| Error::UnknownPackage {
                        name: name.to_string(),
                        span,
                    })?;

                log::debug!("registering package `{name}` with the graph");
                let package = Package::from_bytes(name, version, bytes, state.graph.types_mut())
                    .map_err(|e| Error::PackageParseFailure {
                        name: name.to_string(),
                        span,
                        source: e,
                    })?;

                Ok(state
                    .graph
                    .register_package(package)
                    .expect("package should not exist"))
            }
        }
    }

    fn validate_target(
        &self,
        state: &State,
        path: &ast::PackagePath,
        world: WorldId,
    ) -> ResolutionResult<()> {
        let world = &state.graph.types()[world];
        let mut cache = Default::default();
        let mut checker = SubtypeChecker::new(&mut cache);

        // The output is allowed to import a subset of the world's imports
        checker.invert();
        for (name, import) in state
            .graph
            .node_ids()
            .filter_map(|n| match &state.graph[n].kind {
                NodeKind::Import(name) => Some((name, n)),
                _ => None,
            })
        {
            let expected = world
                .imports
                .get(name)
                .ok_or_else(|| Error::ImportNotInTarget {
                    name: name.clone(),
                    world: path.string.to_owned(),
                    span: state.import_spans[&import],
                })?;

            checker
                .is_subtype(
                    expected.promote(),
                    state.graph.types(),
                    state.graph[import].item_kind,
                    state.graph.types(),
                )
                .map_err(|e| Error::TargetMismatch {
                    kind: ExternKind::Import,
                    name: name.clone(),
                    world: path.string.to_owned(),
                    span: state.import_spans[&import],
                    source: e,
                })?;
        }

        checker.revert();

        // The output must export every export in the world
        for (name, expected) in &world.exports {
            let export =
                state
                    .graph
                    .get_export(name)
                    .ok_or_else(|| Error::MissingTargetExport {
                        name: name.clone(),
                        world: path.string.to_owned(),
                        kind: expected.desc(state.graph.types()).to_string(),
                        span: path.span,
                    })?;

            checker
                .is_subtype(
                    state.graph[export].item_kind,
                    state.graph.types(),
                    expected.promote(),
                    state.graph.types(),
                )
                .map_err(|e| Error::TargetMismatch {
                    kind: ExternKind::Export,
                    name: name.clone(),
                    world: path.string.to_owned(),
                    span: state.export_spans[&export],
                    source: e,
                })?;
        }

        Ok(())
    }
}
