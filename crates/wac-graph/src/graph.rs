use crate::encoding::{State, TypeEncoder};
use indexmap::{IndexMap, IndexSet};
use petgraph::{algo::toposort, graphmap::DiGraphMap, Direction};
use semver::Version;
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    fmt::Write,
    ops::Index,
    str::FromStr,
};
use thiserror::Error;
use wac_types::{
    BorrowedKey, BorrowedPackageKey, ExternKind, ItemKind, Package, PackageKey, SubtypeCheck,
    SubtypeChecker, Type, TypeAggregator, Types,
};
use wasm_encoder::{
    Alias, ComponentBuilder, ComponentExportKind, ComponentNameSection, ComponentTypeRef,
    ComponentValType, NameMap, TypeBounds,
};
use wasmparser::{
    names::{ComponentName, ComponentNameKind},
    BinaryReaderError, Validator, WasmFeatures,
};

struct PackagePath<'a> {
    package: &'a str,
    version: Option<Version>,
    segments: &'a str,
}

impl<'a> PackagePath<'a> {
    fn new(path: &'a str) -> GraphResult<Self> {
        let (package, segments) =
            path.split_once('/')
                .ok_or_else(|| Error::UnqualifiedPackagePath {
                    path: path.to_string(),
                })?;

        let (package, version) = package
            .split_once('@')
            .map(|(n, v)| (n, Version::from_str(v).map(Some).map_err(|e| (v, e))))
            .unwrap_or((package, Ok(None)));

        let version = version.map_err(|(version, error)| Error::InvalidPackageVersion {
            version: version.to_string(),
            error,
        })?;

        Ok(Self {
            package,
            version,
            segments,
        })
    }
}

/// Represents an error that can occur when working with a composition graph.
#[derive(Debug, Error)]
pub enum Error {
    /// The specified type was not defined in the graph.
    #[error("the specified type was not defined in the graph.")]
    TypeNotDefined {
        /// The type that was not defined in the graph.
        ty: Type,
    },
    /// A resource type cannot be defined in the graph.
    #[error("a resource type cannot be defined in the graph")]
    CannotDefineResource,
    /// The specified package path is not fully-qualified.
    #[error("package path `{path}` is not a fully-qualified package path")]
    UnqualifiedPackagePath {
        /// The path that was invalid.
        path: String,
    },
    /// The specified package version is invalid.
    #[error("package version `{version}` is not a valid semantic version")]
    InvalidPackageVersion {
        /// The version that was invalid.
        version: String,
        /// The error that occurred while parsing the package version.
        #[source]
        error: semver::Error,
    },
    /// The specified package has not been registered.
    #[error("package `{package}` has not been registered with the graph", package = BorrowedPackageKey::from_name_and_version(.package, .version.as_ref()))]
    UnknownPackage {
        /// The name of the unknown package.
        package: String,
        /// The version of the unknown package.
        version: Option<Version>,
    },
    /// The package does not export an item for the specified path.
    #[error("package `{package}` does not export an item for path `{path}`")]
    PackageMissingExport {
        /// The package with the missing export.
        package: String,
        /// The path that was missing.
        path: String,
    },
    /// The specified package identifier is invalid.
    #[error("the specified package identifier is invalid")]
    InvalidPackageId,
    /// The specified node identifier is invalid.
    #[error("the specified node identifier is invalid")]
    InvalidNodeId,
    /// The package is already registered in the graph.
    #[error("package `{key}` has already been registered in the graph")]
    PackageAlreadyRegistered {
        /// The key representing the already registered package
        key: PackageKey,
    },
    /// An extern name already exists in the graph.
    #[error("{kind} name `{name}` already exists in the graph")]
    ExternAlreadyExists {
        /// The kind of extern.
        kind: ExternKind,
        /// The name of the existing extern.
        name: String,
    },
    /// An invalid extern name was given.
    #[error("{kind} name `{name}` is not a valid extern name")]
    InvalidExternName {
        /// The name of the export.
        name: String,
        /// The kind of extern.
        kind: ExternKind,
        /// The underlying validation error.
        #[source]
        source: anyhow::Error,
    },
    /// The node is not an instance.
    #[error("expected node to be an instance, but the node is a {kind}")]
    NodeIsNotAnInstance {
        /// The node that is not an instance.
        node: NodeId,
        /// The kind of the node.
        kind: String,
    },
    /// The node is not an instantiation.
    #[error("the specified node is not an instantiation")]
    NodeIsNotAnInstantiation {
        /// The node that is not an instantiation.
        node: NodeId,
    },
    /// The instance does not export an item with the given name.
    #[error("instance does not have an export named `{export}`")]
    InstanceMissingExport {
        /// The instance node that is missing the export.
        node: NodeId,
        /// The export that was missing.
        export: String,
    },
    /// The provided argument name is invalid.
    #[error("argument name `{name}` is not an import of package `{package}`")]
    InvalidArgumentName {
        /// The instantiation node that does not have the provided argument name.
        node: NodeId,
        /// The name of the invalid argument.
        name: String,
        /// The name of the package that does not have the argument.
        package: String,
    },
    /// The source type does not match the target argument type.
    #[error("mismatched instantiation argument `{name}`")]
    ArgumentTypeMismatch {
        /// The name of the argument.
        name: String,
        /// The source of the error.
        #[source]
        source: anyhow::Error,
    },
    /// The argument has already satisfied.
    #[error("argument `{name}` has already satisfied")]
    ArgumentAlreadySatisfied {
        /// The target node that already has the satisfied argument.
        node: NodeId,
        /// The name of the argument that is already satisfied.
        name: String,
    },
    /// The graph contains a cycle.
    #[error("the graph contains a cycle and cannot be encoded")]
    GraphContainsCycle {
        /// The node where the cycle was detected.
        node: NodeId,
    },
    /// The encoding of the graph failed validation.
    #[error("the encoding of the graph failed validation")]
    EncodingValidationFailure {
        /// The source of the validation error.
        #[source]
        source: BinaryReaderError,
    },
    /// The node cannot be unmarked from export as it is a type definition.
    #[error("the node cannot be unmarked from export as it is a type definition")]
    MustExportDefinition,
    /// An implicit import on an instantiation conflicts with an explicit import node.
    #[error("an instantiation node implicitly imports an item named `{name}`, but it conflicts with an explicit import node of the same name")]
    ImplicitImportConfig {
        /// The existing import node.
        import: NodeId,
        /// The instantiation node with the implicit import
        instantiation: NodeId,
        /// The name of the conflicting import.
        name: String,
    },
    /// An error occurred while aggregating a type.
    #[error("failed to aggregate type definition for import `{import}`")]
    TypeAggregationError {
        /// The name of the import being aggregated.
        import: String,
        /// The type aggregation error.
        #[source]
        source: anyhow::Error,
    },
}

/// An alias for the result type used by the composition graph.
pub type GraphResult<T> = std::result::Result<T, Error>;

/// An identifier for a package in a composition graph.
#[derive(Debug, Copy, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct PackageId {
    /// The index into the graph's packages list.
    index: usize,
    /// The generation of the package.
    ///
    /// This is used to invalidate identifiers on package removal.
    generation: usize,
}

/// An identifier for a node in a composition graph.
#[derive(Debug, Copy, Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
pub struct NodeId {
    /// The index into the graph's node list.
    index: usize,
    /// The generation of the node.
    ///
    /// This is used to invalidate identifiers on node removal.
    generation: usize,
}

#[derive(Debug, Clone)]
enum NodeKind {
    /// The node is a type definition.
    Definition,
    /// The node is an import of an item.
    ///
    /// The string is the import name.
    Import(String),
    /// The node is an instantiation of a package.
    ///
    /// The set is the currently satisfied argument indexes.
    Instantiation(HashSet<usize>),
    /// The node is an alias of an export of an instance.
    Alias,
}

/// Represents a package registered with a composition graph.
#[derive(Debug, Clone)]
struct RegisteredPackage {
    /// The underlying package.
    package: Option<Package>,
    /// The nodes associated with the package.
    nodes: HashSet<NodeId>,
    /// The generation of the package.
    ///
    /// The generation is incremented each time a package is removed from the graph.
    ///
    /// This ensures referring package identifiers are invalidated when a package is removed.
    generation: usize,
}

impl RegisteredPackage {
    fn new(generation: usize) -> Self {
        Self {
            package: None,
            nodes: Default::default(),
            generation,
        }
    }
}

#[derive(Debug, Clone)]
struct NodeData<C> {
    /// The node kind.
    kind: NodeKind,
    /// The package associated with the node, if any.
    package: Option<PackageId>,
    /// The item kind of the node.
    item_kind: ItemKind,
    /// The optional name to associate with the node.
    ///
    /// When the graph is encoded, node names are recorded in a `names` custom section.
    name: Option<String>,
    /// The name to use for exporting the node.
    export: Option<String>,
    /// The aliased nodes from this node.
    aliases: HashMap<String, NodeId>,
    /// The context associated with the node.
    context: C,
}

impl<C> NodeData<C> {
    fn new(kind: NodeKind, item_kind: ItemKind, package: Option<PackageId>, context: C) -> Self {
        Self {
            kind,
            item_kind,
            package,
            name: None,
            export: None,
            aliases: Default::default(),
            context,
        }
    }

    fn import_name(&self) -> Option<&str> {
        match &self.kind {
            NodeKind::Import(name) => Some(name),
            _ => None,
        }
    }

    fn add_satisfied_arg(&mut self, index: usize) {
        match &mut self.kind {
            NodeKind::Instantiation(satisfied) => {
                let inserted = satisfied.insert(index);
                assert!(inserted);
            }
            _ => unreachable!(),
        }
    }

    fn remove_satisfied_arg(&mut self, index: usize) {
        match &mut self.kind {
            NodeKind::Instantiation(satisfied) => {
                let removed = satisfied.remove(&index);
                assert!(removed);
            }
            _ => unreachable!(),
        }
    }

    fn is_arg_satisfied(&self, index: usize) -> bool {
        match &self.kind {
            NodeKind::Instantiation(satisfied) => satisfied.contains(&index),
            _ => unreachable!(),
        }
    }
}

/// Represents a node in a composition graph.
#[derive(Debug, Clone)]
struct Node<C> {
    /// The data associated with the node.
    data: Option<NodeData<C>>,
    /// The generation of the node.
    ///
    /// The generation is incremented each time the node is removed from the graph.
    ///
    /// This ensures referring node identifiers are invalidated when a node is removed.
    generation: usize,
}

impl<C> Node<C> {
    fn new(generation: usize) -> Self {
        Self {
            data: None,
            generation,
        }
    }
}

/// Represents an edge in a composition graph.
#[derive(Debug, Clone)]
enum Edge {
    /// The edge is from an instance to an aliased exported item.
    ///
    /// The data is the index of the export on the source node.
    Alias(usize),
    /// The edge is from any node to an instantiation node.
    ///
    /// The set contains import indexes on the target node that are
    /// satisfied by the source node.
    Argument(IndexSet<usize>),
}

/// Represents information about a node in a composition graph.
pub struct NodeInfo<'a, C> {
    /// The types collection for the node's item kind.
    pub types: &'a Types,
    /// The item kind of the node.
    pub kind: ItemKind,
    /// The context of the node.
    pub context: &'a C,
    /// The optional name of the node.
    pub name: Option<&'a str>,
    /// The aliases from this node.
    pub aliases: &'a HashMap<String, NodeId>,
    /// The export name of the node.
    ///
    /// If the node is not exported, this field will be `None`.
    pub export: Option<&'a str>,
}

/// Represents a composition graph.
///
/// A composition graph is a directed acyclic graph (DAG) that represents a WebAssembly composition.
///
/// Types may be defined directly in a composition graph or referenced from packages registered with
/// the graph.
///
/// There are four supported node types:
///
/// * a *type definition node* representing the definition of an exported named type.
/// * an *import node* representing an imported item.
/// * an *instantiation node* representing an instantiation of a package.
/// * an *alias node* representing an alias of an exported item from an instance.
///
/// There are two supported edge types:
///
/// * an *alias edge* from an any node that is an instance to an alias node; alias edges are
///   implicitly added to the graph when an alias node is added.
/// * an *instantiation argument edge* from any node to an instantiation node; instantiation
///   argument edges contain a set of instantiation arguments satisfied by the target node;
///   unsatisfied arguments are automatically imported when encoding the composition graph.
///
/// Any node in the graph may be marked to be exported from the encoded graph; note that
/// type definition nodes are _always_ exported and may not be unmarked.
///
/// The type parameter `C` represents the context type to associate with each node in the
/// graph; a node's context may be retrieved by indexing the graph with a node identifier.
#[derive(Clone)]
pub struct CompositionGraph<C = ()> {
    /// The underlying graph data structure.
    graph: DiGraphMap<NodeId, Edge>,
    /// The import nodes of the graph.
    imports: HashMap<String, NodeId>,
    /// The set of used export names.
    exports: IndexMap<String, NodeId>,
    /// The map of package keys to package ids.
    package_map: HashMap<PackageKey, PackageId>,
    /// The registered packages.
    packages: Vec<RegisteredPackage>,
    /// The list of free entries in the packages list.
    free_packages: Vec<usize>,
    /// The nodes in the graph.
    nodes: Vec<Node<C>>,
    /// The list of free entries in the nodes list.
    free_nodes: Vec<usize>,
    /// The types that are directly defined by the graph.
    types: Types,
    /// The cache used for subtype checks.
    type_check_cache: HashSet<(ItemKind, ItemKind)>,
}

impl<C> CompositionGraph<C> {
    /// Creates a new composition graph.
    pub fn new() -> Self {
        Self::default()
    }

    /// Gets a reference to the type collection of the graph.
    pub fn types(&self) -> &Types {
        &self.types
    }

    /// Gets a mutable reference to the type collection of the graph.
    ///
    /// This type collection is used to define types directly in the graph.
    pub fn types_mut(&mut self) -> &mut Types {
        &mut self.types
    }

    /// Gets the identifiers for every node in the graph.
    pub fn nodes(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.nodes.iter().enumerate().filter_map(|(i, n)| {
            n.data.as_ref()?;
            Some(NodeId {
                index: i,
                generation: n.generation,
            })
        })
    }

    /// Registers a package with the graph.
    ///
    /// A package can be used to create instantiations, but are not
    /// directly part of the graph.
    pub fn register_package(&mut self, package: wac_types::Package) -> GraphResult<PackageId> {
        let key = PackageKey::new(&package);
        if self.package_map.contains_key(&key) {
            return Err(Error::PackageAlreadyRegistered { key });
        }

        let id = self.alloc_package(package);
        let prev = self.package_map.insert(key, id);
        assert!(prev.is_none());
        Ok(id)
    }

    /// Unregisters a package from the graph.
    ///
    /// Any edges and nodes associated with the package are also removed.
    pub fn unregister_package(&mut self, id: PackageId) -> GraphResult<()> {
        if self.get_package(id).is_none() {
            return Err(Error::InvalidPackageId);
        }

        self.free_package(id);
        Ok(())
    }

    /// Gets a package that was registered with the graph.
    pub fn get_package(&self, id: PackageId) -> Option<&Package> {
        let PackageId { index, generation } = id;
        let entry = &self.packages[index];
        if entry.generation != generation {
            return None;
        }

        entry.package.as_ref()
    }

    /// Gets the registered package of the given package name and version.
    pub fn get_package_by_name(
        &self,
        name: &str,
        version: Option<&Version>,
    ) -> Option<(PackageId, &wac_types::Package)> {
        let key: BorrowedPackageKey<'_> = BorrowedPackageKey::from_name_and_version(name, version);
        let id = self.package_map.get(&key as &dyn BorrowedKey)?;
        Some((*id, self.packages[id.index].package.as_ref().unwrap()))
    }

    /// Adds a *type definition node* to the graph.
    ///
    /// The graph must not already have a node exported with the same name.
    ///
    /// The specified type must have been added to the graph's type collection.
    pub fn add_type_definition_node(
        &mut self,
        name: impl Into<String>,
        ty: Type,
        context: C,
    ) -> GraphResult<NodeId> {
        if !self.types.contains(ty) {
            return Err(Error::TypeNotDefined { ty });
        }

        if let Type::Resource(_) = ty {
            return Err(Error::CannotDefineResource);
        }

        let name = name.into();
        if self.exports.contains_key(&name) {
            return Err(Error::ExternAlreadyExists {
                kind: ExternKind::Export,
                name,
            });
        }

        // Ensure that the given name is a valid extern name
        ComponentName::new(&name, 0).map_err(|e| {
            let msg = e.to_string();
            Error::InvalidExternName {
                name: name.to_string(),
                kind: ExternKind::Export,
                source: anyhow::anyhow!(
                    "{msg}",
                    msg = msg.strip_suffix(" (at offset 0x0)").unwrap_or(&msg)
                ),
            }
        })?;

        let mut data = NodeData::new(NodeKind::Definition, ItemKind::Type(ty), None, context);
        data.export = Some(name.clone());

        let id = self.alloc_node(data);
        self.graph.add_node(id);

        let prev = self.exports.insert(name, id);
        assert!(prev.is_none());
        Ok(id)
    }

    /// Adds an *import node* to the graph.
    ///
    /// If an import with the same name already exists, an error is returned.
    ///
    /// The specified item kind must already have been defined in the graph.
    pub fn add_import_node(
        &mut self,
        name: impl Into<String>,
        kind: ItemKind,
        context: C,
    ) -> GraphResult<NodeId> {
        let ty = kind.ty();
        if !self.types.contains(ty) {
            return Err(Error::TypeNotDefined { ty });
        }

        self.add_import(name, None, kind, context)
    }

    /// Adds an *import node* to the graph with the item kind specified by package path.
    ///
    /// An error is returned if an import with the same name already exists or if the
    /// specified package path is invalid.
    pub fn add_import_node_by_path(
        &mut self,
        name: impl Into<String>,
        path: &str,
        context: C,
    ) -> GraphResult<NodeId> {
        let path = PackagePath::new(path)?;
        let (package_id, package) = self
            .get_package_by_name(path.package, path.version.as_ref())
            .ok_or_else(|| Error::UnknownPackage {
                package: path.package.to_string(),
                version: path.version,
            })?;

        let mut item_kind = None;
        for segment in path.segments.split('/') {
            item_kind = match item_kind {
                Some(ItemKind::Instance(id)) => package.types()[id].exports.get(segment).copied(),
                None => package.export(segment),
                _ => None,
            };

            if item_kind.is_none() {
                break;
            }
        }

        let item_kind = item_kind
            .ok_or_else(|| Error::PackageMissingExport {
                package: path.package.to_string(),
                path: path.segments.to_string(),
            })?
            .promote();

        self.add_import(name, Some(package_id), item_kind, context)
    }

    /// Adds an *instantiation node* to the graph.
    ///
    /// Initially the instantiation will have no connected arguments.
    ///
    /// Use `add_argument_edge` to add an edge between an argument and the
    /// instantiation.
    pub fn add_instantiation_node(&mut self, id: PackageId, context: C) -> GraphResult<NodeId> {
        let package = self.get_package(id).ok_or(Error::InvalidPackageId)?;
        let node = self.alloc_node(NodeData::new(
            NodeKind::Instantiation(Default::default()),
            ItemKind::Instance(package.instance_type()),
            Some(id),
            context,
        ));
        Ok(self.graph.add_node(node))
    }

    /// Adds an *alias node* to the graph.
    ///
    /// The provided node must be an instance and the export name must match an export
    /// of the instance.
    ///
    /// If an alias already exists for the export, the existing alias node will be returned.
    ///
    /// An implicit *alias edge* will be added from the instance to the alias node.
    pub fn add_alias_node(
        &mut self,
        source: NodeId,
        export: &str,
        context: C,
    ) -> GraphResult<NodeId> {
        let source_data = self
            .get_node(source)
            .ok_or(Error::InvalidNodeId)?
            .data
            .as_ref()
            .unwrap();

        if let Some(id) = source_data.aliases.get(export) {
            return Ok(*id);
        }

        // Ensure the source is an instance
        let types = self.node_types(source_data);
        let exports = match source_data.item_kind {
            ItemKind::Instance(id) => &types[id].exports,
            _ => {
                return Err(Error::NodeIsNotAnInstance {
                    node: source,
                    kind: source_data.item_kind.desc(types).to_string(),
                });
            }
        };

        // Ensure the export exists
        let (index, _, kind) =
            exports
                .get_full(export)
                .ok_or_else(|| Error::InstanceMissingExport {
                    node: source,
                    export: export.to_string(),
                })?;

        // Allocate the alias node
        let aliased = self.alloc_node(NodeData::new(
            NodeKind::Alias,
            *kind,
            source_data.package,
            context,
        ));

        let prev = self.nodes[source.index]
            .data
            .as_mut()
            .unwrap()
            .aliases
            .insert(export.to_string(), aliased);
        assert!(prev.is_none());

        self.graph.add_node(aliased);
        let prev = self.graph.add_edge(source, aliased, Edge::Alias(index));
        assert!(prev.is_none());
        Ok(aliased)
    }

    /// Gets the source node and export name of an alias node.
    ///
    /// Returns `None` if the given id is invalid or if the node is not an alias.
    pub fn get_alias_source(&self, node: NodeId) -> Option<(NodeId, &str)> {
        for (s, t, edge) in self.graph.edges_directed(node, Direction::Incoming) {
            assert_eq!(t, node);

            if let Edge::Alias(index) = edge {
                let data = self.node_data(s);
                match data.item_kind {
                    ItemKind::Instance(id) => {
                        let types = self.node_types(data);
                        let export = types[id].exports.get_index(*index).unwrap().0;
                        return Some((s, export));
                    }
                    _ => unreachable!("alias source should be an instance"),
                }
            }
        }

        None
    }

    /// Gets the satisfied arguments of an instantiation node.
    ///
    /// Returns an iterator over the argument names and the node used to satisfy the argument.
    ///
    /// If the node identifier is invalid or if the node is not an instantiation node, an
    /// empty iterator is returned.
    pub fn get_arguments(&self, node: NodeId) -> impl Iterator<Item = (&str, NodeId)> {
        self.graph
            .edges_directed(node, Direction::Incoming)
            .filter_map(|(s, t, e)| {
                let target = self.node_data(t);
                let imports = match target.kind {
                    NodeKind::Instantiation(_) => {
                        let package = &self.packages[target.package?.index].package.as_ref()?;
                        &package.types()[package.ty()].imports
                    }
                    _ => return None,
                };

                match e {
                    Edge::Alias(_) => None,
                    Edge::Argument(indexmap) => Some(
                        indexmap
                            .iter()
                            .map(move |i| (imports.get_index(*i).unwrap().0.as_ref(), s)),
                    ),
                }
            })
            .flatten()
    }

    /// Gets information about a node in the graph.
    ///
    /// Returns `None` if the specified node identifier is invalid.
    pub fn get_node_info(&self, id: NodeId) -> Option<NodeInfo<C>> {
        self.get_node(id)?;
        let data = self.node_data(id);

        Some(NodeInfo {
            types: self.node_types(data),
            kind: data.item_kind,
            context: &data.context,
            name: data.name.as_deref(),
            aliases: &data.aliases,
            export: data.export.as_deref(),
        })
    }

    /// Sets the name of a node in the graph.
    ///
    /// Node names are recorded in a `names` custom section when the graph is encoded.
    pub fn set_node_name(&mut self, id: NodeId, name: impl Into<String>) -> GraphResult<()> {
        self.get_node(id).ok_or(Error::InvalidPackageId)?;
        self.node_data_mut(id).name = Some(name.into());
        Ok(())
    }

    /// Marks the given node for export when the composition graph is encoded.
    pub fn export_node(&mut self, id: NodeId, name: impl Into<String>) -> GraphResult<()> {
        self.get_node(id).ok_or(Error::InvalidPackageId)?;

        let name = name.into();
        if self.exports.contains_key(&name) {
            return Err(Error::ExternAlreadyExists {
                kind: ExternKind::Export,
                name,
            });
        }

        let map_reader_err = |e: BinaryReaderError| {
            let msg = e.to_string();
            Error::InvalidExternName {
                name: name.to_string(),
                kind: ExternKind::Export,
                source: anyhow::anyhow!(
                    "{msg}",
                    msg = msg.strip_suffix(" (at offset 0x0)").unwrap_or(&msg)
                ),
            }
        };

        // Ensure that the given export name is a valid extern name
        match ComponentName::new(&name, 0).map_err(map_reader_err)?.kind() {
            ComponentNameKind::Hash(_)
            | ComponentNameKind::Url(_)
            | ComponentNameKind::Dependency(_) => {
                return Err(Error::InvalidExternName {
                    name: name.to_string(),
                    kind: ExternKind::Export,
                    source: anyhow::anyhow!("export name cannot be a hash, url, or dependency"),
                });
            }
            _ => {}
        };

        self.node_data_mut(id).export = Some(name.clone());

        let prev = self.exports.insert(name, id);
        assert!(prev.is_none());
        Ok(())
    }

    /// Unmarks the given node from export.
    ///
    /// The node cannot be a _type definition node_ as type definitions are
    /// always exported.
    pub fn unexport_node(&mut self, id: NodeId) -> GraphResult<()> {
        self.get_node(id).ok_or(Error::InvalidPackageId)?;

        let data = self.node_data_mut(id);
        if let NodeKind::Definition = data.kind {
            return Err(Error::MustExportDefinition);
        }

        if let Some(name) = data.export.take() {
            let removed = self.exports.swap_remove(&name);
            assert!(removed.is_some());
        }

        Ok(())
    }

    /// Removes a node from the graph.
    ///
    /// All incoming and outgoing edges of the node are also removed.
    ///
    /// If the node has aliases, the aliased nodes are also removed.
    ///
    /// Returns `true` if the node was removed, otherwise returns `false`.
    pub fn remove_node(&mut self, node: NodeId) -> bool {
        if !self.graph.remove_node(node) {
            return false;
        }

        self.free_node(node, false);
        true
    }

    /// Adds an *instantiation argument edge* to the graph.
    ///
    /// The target node must be an instantiation node.
    ///
    /// The source node must be type-compatible with the argument of the target node.
    ///
    /// The argument must be a valid import on the target and not already have an
    /// incoming edge from a different source node.
    pub fn add_argument_edge(
        &mut self,
        source: NodeId,
        target: NodeId,
        argument: &str,
    ) -> GraphResult<()> {
        fn add_edge<C>(
            graph: &mut CompositionGraph<C>,
            source: NodeId,
            target: NodeId,
            argument: &str,
            cache: &mut HashSet<(ItemKind, ItemKind)>,
        ) -> GraphResult<()> {
            // Ensure the target is an instantiation node
            let target_data = graph
                .get_node(target)
                .ok_or(Error::InvalidNodeId)?
                .data
                .as_ref()
                .unwrap();

            if !matches!(target_data.kind, NodeKind::Instantiation(_)) {
                return Err(Error::NodeIsNotAnInstantiation { node: target });
            }

            // Ensure the argument is a valid import of the target package
            let target_types = graph.node_types(target_data);
            let package = graph.packages[target_data.package.unwrap().index]
                .package
                .as_ref()
                .unwrap();
            let package_type = &package.types()[package.ty()];

            // Ensure the argument isn't already satisfied
            let (argument_index, _, argument_kind) = package_type
                .imports
                .get_full(argument)
                .ok_or(Error::InvalidArgumentName {
                    node: target,
                    name: argument.to_string(),
                    package: package.name().to_string(),
                })?;

            for (s, t, edge) in graph.graph.edges_directed(target, Direction::Incoming) {
                assert_eq!(t, target);
                match edge {
                    Edge::Alias(_) => {
                        unreachable!(
                            "incoming alias edges should not exist for instantiation nodes"
                        )
                    }
                    Edge::Argument(set) => {
                        if set.contains(&argument_index) {
                            if s == source {
                                return Ok(());
                            }

                            return Err(Error::ArgumentAlreadySatisfied {
                                node: target,
                                name: argument.to_string(),
                            });
                        }
                    }
                }
            }

            // Perform a subtype check on the source and target
            let source_data = graph
                .get_node(source)
                .ok_or(Error::InvalidNodeId)?
                .data
                .as_ref()
                .unwrap();
            let source_types = graph.node_types(source_data);

            let mut checker = SubtypeChecker::new(cache);
            checker
                .is_subtype(
                    source_data.item_kind,
                    source_types,
                    *argument_kind,
                    target_types,
                    SubtypeCheck::Covariant,
                )
                .map_err(|e| Error::ArgumentTypeMismatch {
                    name: argument.to_string(),
                    source: e,
                })?;

            // Finally, insert the argument edge
            if let Some(edge) = graph.graph.edge_weight_mut(source, target) {
                match edge {
                    Edge::Alias(_) => {
                        unreachable!("alias edges should not exist for instantiation nodes")
                    }
                    Edge::Argument(set) => {
                        let inserted = set.insert(argument_index);
                        assert!(inserted);
                    }
                }
            } else {
                let mut set = IndexSet::new();
                set.insert(argument_index);
                graph.graph.add_edge(source, target, Edge::Argument(set));
            }

            graph.nodes[target.index]
                .data
                .as_mut()
                .unwrap()
                .add_satisfied_arg(argument_index);

            Ok(())
        }

        // Temporarily take ownership of the cache to avoid borrowing issues
        let mut cache = std::mem::take(&mut self.type_check_cache);
        let result = add_edge(self, source, target, argument, &mut cache);
        self.type_check_cache = cache;
        result
    }

    /// Removes an *instantiation argument edge* from the graph.
    ///
    /// The target node must be an instantiation.
    ///
    /// The argument must be a valid import on the target.
    ///
    /// If the argument is not connected to the source, then this function
    /// will be a no-op.
    pub fn remove_argument_edge(
        &mut self,
        source: NodeId,
        target: NodeId,
        argument: &str,
    ) -> GraphResult<()> {
        // Ensure the target is an instantiation node
        let target_data = self
            .get_node(target)
            .ok_or(Error::InvalidNodeId)?
            .data
            .as_ref()
            .unwrap();
        if !matches!(target_data.kind, NodeKind::Instantiation(_)) {
            return Err(Error::NodeIsNotAnInstantiation { node: target });
        }

        // Ensure the argument is a valid import of the target package
        let package = self.packages[target_data.package.unwrap().index]
            .package
            .as_ref()
            .unwrap();
        let package_type = &package.types()[package.ty()];

        let argument_index =
            package_type
                .imports
                .get_index_of(argument)
                .ok_or(Error::InvalidArgumentName {
                    node: target,
                    name: argument.to_string(),
                    package: package.name().to_string(),
                })?;

        // Finally remove the argument edge if a connection exists
        let remove_edge = if let Some(edge) = self.graph.edge_weight_mut(source, target) {
            match edge {
                Edge::Alias(_) => {
                    unreachable!("alias edges should not exist for instantiation nodes")
                }
                Edge::Argument(set) => {
                    set.swap_remove(&argument_index);
                    self.nodes[target.index]
                        .data
                        .as_mut()
                        .unwrap()
                        .remove_satisfied_arg(argument_index);
                    set.is_empty()
                }
            }
        } else {
            false
        };

        if remove_edge {
            self.graph.remove_edge(source, target);
        }

        Ok(())
    }

    /// Encodes the composition graph as a new WebAssembly component.
    ///
    /// An error will be returned if the graph contains a dependency cycle.
    pub fn encode(&self, options: EncodeOptions) -> GraphResult<Vec<u8>> {
        let bytes = CompositionGraphEncoder::new(self).encode(options)?;

        if options.validate {
            Validator::new_with_features(WasmFeatures {
                component_model: true,
                ..Default::default()
            })
            .validate_all(&bytes)
            .map_err(|e| Error::EncodingValidationFailure { source: e })?;
        }

        Ok(bytes)
    }

    /// Decodes a composition graph from the bytes of a WebAssembly component.
    pub fn decode(_data: &[u8]) -> GraphResult<CompositionGraph> {
        todo!("decoding of composition graphs is not yet implemented")
    }

    fn add_import(
        &mut self,
        name: impl Into<String>,
        package: Option<PackageId>,
        kind: ItemKind,
        context: C,
    ) -> GraphResult<NodeId> {
        let name = name.into();
        if self.imports.contains_key(&name) {
            return Err(Error::ExternAlreadyExists {
                kind: ExternKind::Import,
                name,
            });
        }

        // Ensure that the given import name is a valid extern name
        ComponentName::new(&name, 0).map_err(|e| {
            let msg = e.to_string();
            Error::InvalidExternName {
                name: name.to_string(),
                kind: ExternKind::Import,
                source: anyhow::anyhow!(
                    "{msg}",
                    msg = msg.strip_suffix(" (at offset 0x0)").unwrap_or(&msg)
                ),
            }
        })?;

        let id = self.alloc_node(NodeData::new(
            NodeKind::Import(name.clone()),
            kind,
            package,
            context,
        ));
        self.graph.add_node(id);

        let prev = self.imports.insert(name, id);
        assert!(prev.is_none());
        Ok(id)
    }

    fn alloc_package(&mut self, package: wac_types::Package) -> PackageId {
        let (index, entry) = if let Some(index) = self.free_packages.pop() {
            let entry = &mut self.packages[index];
            assert!(entry.package.is_none());
            (index, entry)
        } else {
            let index = self.packages.len();
            self.packages.push(RegisteredPackage::new(0));
            (index, &mut self.packages[index])
        };

        entry.package = Some(package);

        PackageId {
            index,
            generation: entry.generation,
        }
    }

    fn free_package(&mut self, id: PackageId) {
        debug_assert_eq!(
            self.packages[id.index].generation, id.generation,
            "invalid package identifier"
        );

        // Free all nodes associated with the package
        let nodes = std::mem::take(&mut self.packages[id.index].nodes);
        for node in nodes {
            let removed = self.graph.remove_node(node);
            assert!(removed);
            self.free_node(node, true);
        }

        // Remove the package from the package map
        let entry = &mut self.packages[id.index];
        let prev = self
            .package_map
            .remove(&BorrowedPackageKey::new(entry.package.as_ref().unwrap()) as &dyn BorrowedKey);
        assert!(prev.is_some());

        // Finally free the package
        *entry = RegisteredPackage::new(entry.generation.wrapping_add(1));
        self.free_packages.push(id.index);
    }

    fn alloc_node(&mut self, data: NodeData<C>) -> NodeId {
        let (index, node) = if let Some(index) = self.free_nodes.pop() {
            let node = &mut self.nodes[index];
            assert!(node.data.is_none());
            (index, node)
        } else {
            let index = self.nodes.len();
            self.nodes.push(Node::new(0));
            (index, &mut self.nodes[index])
        };

        let id = NodeId {
            index,
            generation: node.generation,
        };

        if let Some(package) = data.package {
            debug_assert_eq!(
                self.packages[package.index].generation, package.generation,
                "invalid package identifier"
            );

            let added = self.packages[package.index].nodes.insert(id);
            assert!(added);
        }

        node.data = Some(data);
        id
    }

    fn get_node(&self, id: NodeId) -> Option<&Node<C>> {
        let NodeId { index, generation } = id;
        let node = self.nodes.get(index)?;
        if node.generation != generation {
            return None;
        }

        assert!(node.data.is_some());
        Some(node)
    }

    fn free_node(&mut self, id: NodeId, package_removed: bool) {
        debug_assert_eq!(
            self.nodes[id.index].generation, id.generation,
            "invalid node identifier"
        );

        // Free the node
        let next = self.nodes[id.index].generation.wrapping_add(1);
        let node = std::mem::replace(&mut self.nodes[id.index], Node::new(next));
        let data = node.data.unwrap();

        // If we're not freeing the node as a result of removing a package,
        // then remove it from the package and also recurse on any aliases.
        if !package_removed {
            // Remove the node from the package
            if let Some(pkg) = data.package {
                debug_assert_eq!(
                    self.packages[pkg.index].generation, pkg.generation,
                    "invalid package identifier"
                );

                let removed = self.packages[pkg.index].nodes.remove(&id);
                assert!(removed);
            }

            // Recursively remove any alias nodes from the graph
            for alias in data.aliases.values() {
                self.remove_node(*alias);
            }
        }

        // Remove any import entries
        if let Some(name) = data.import_name() {
            let removed = self.imports.remove(name);
            assert!(removed.is_some());
        }

        // Finally, add the node to the free list
        self.free_nodes.push(id.index);
    }

    fn node_data(&self, id: NodeId) -> &NodeData<C> {
        self.nodes[id.index].data.as_ref().unwrap()
    }

    fn node_data_mut(&mut self, id: NodeId) -> &mut NodeData<C> {
        self.nodes[id.index].data.as_mut().unwrap()
    }

    fn node_types(&self, data: &NodeData<C>) -> &Types {
        data.package
            .and_then(|id| self.get_package(id))
            .map(|p| p.types())
            .unwrap_or(&self.types)
    }
}

// This is implemented *without* a `C: Default` constraint.
impl<C> Default for CompositionGraph<C> {
    fn default() -> Self {
        Self {
            graph: Default::default(),
            imports: Default::default(),
            exports: Default::default(),
            package_map: Default::default(),
            packages: Default::default(),
            free_packages: Default::default(),
            nodes: Default::default(),
            free_nodes: Default::default(),
            types: Default::default(),
            type_check_cache: Default::default(),
        }
    }
}

impl<C> Index<PackageId> for CompositionGraph<C> {
    type Output = wac_types::Package;

    fn index(&self, id: PackageId) -> &Self::Output {
        self.get_package(id).expect("invalid package identifier")
    }
}

impl<C> Index<NodeId> for CompositionGraph<C> {
    type Output = C;

    fn index(&self, id: NodeId) -> &Self::Output {
        &self
            .get_node(id)
            .expect("node identifier is invalid")
            .data
            .as_ref()
            .unwrap()
            .context
    }
}

/// The options for encoding a composition graph.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct EncodeOptions {
    /// Whether or not to define instantiated components.
    ///
    /// If `false`, components will be imported instead.
    ///
    /// Defaults to `true`.
    pub define_components: bool,

    /// Whether or not to validate the encoded output.
    ///
    /// Defaults to `true`.
    pub validate: bool,
}

impl Default for EncodeOptions {
    fn default() -> Self {
        Self {
            define_components: true,
            validate: true,
        }
    }
}

/// Used to encode a composition graph as a new WebAssembly component.
struct CompositionGraphEncoder<'a, C>(&'a CompositionGraph<C>);

impl<'a, C> CompositionGraphEncoder<'a, C> {
    fn new(graph: &'a CompositionGraph<C>) -> Self {
        Self(graph)
    }

    fn encode(self, options: EncodeOptions) -> GraphResult<Vec<u8>> {
        let mut state = State::new();

        // First populate the state with the implicit instantiation arguments
        self.populate_implicit_args(&mut state)?;

        // Encode each node in the graph in topographical order
        for node in toposort(&self.0.graph, None)
            .map_err(|e| Error::GraphContainsCycle { node: e.node_id() })?
        {
            let data = self.0.node_data(node);
            let index = match &data.kind {
                NodeKind::Definition => self.definition(&mut state, data),
                NodeKind::Import(name) => self.import(&mut state, name, data),
                NodeKind::Instantiation(_) => self.instantiation(&mut state, node, data, options),
                NodeKind::Alias => self.alias(&mut state, node, data),
            };

            let prev = state.node_indexes.insert(node, index);
            assert!(prev.is_none());
        }

        // Encode the exports
        for (name, node) in &self.0.exports {
            let index = state.node_indexes[node];
            let data = self.0.node_data(*node);
            state
                .builder()
                .export(name, data.item_kind.into(), index, None);
        }

        let mut builder = std::mem::take(state.builder());
        self.encode_names(&state, &mut builder);

        Ok(builder.finish())
    }

    fn populate_implicit_args(&self, state: &mut State) -> GraphResult<()> {
        let mut aggregator = TypeAggregator::default();
        let mut arguments = Vec::new();
        let mut encoded = HashMap::new();
        let mut cache = Default::default();

        // Enumerate the instantiation nodes and populate the import types
        for node in self.0.nodes() {
            let data = self.0.node_data(node);
            if !matches!(data.kind, NodeKind::Instantiation(_)) {
                continue;
            }

            let package = self.0.get_package(data.package.unwrap()).unwrap();
            let world = &package.types()[package.ty()];

            // Go through the unsatisfied arguments and import them
            for (_, (name, kind)) in world
                .imports
                .iter()
                .enumerate()
                .filter(|(i, _)| !data.is_arg_satisfied(*i))
            {
                if let Some(import) = self.0.imports.get(name).copied() {
                    return Err(Error::ImplicitImportConfig {
                        import,
                        instantiation: node,
                        name: name.to_string(),
                    });
                }

                aggregator = aggregator
                    .aggregate(name, package.types(), *kind, &mut cache)
                    .map_err(|e| Error::TypeAggregationError {
                        import: name.clone(),
                        source: e,
                    })?;
                arguments.push((node, name));
            }
        }

        // Next encode the imports
        let encoder = TypeEncoder::new(aggregator.types());
        for (name, kind) in aggregator.iter() {
            let ty = encoder.ty(state, kind.ty(), None);
            let index = state.builder().import(
                name,
                match kind {
                    ItemKind::Type(_) => ComponentTypeRef::Type(TypeBounds::Eq(ty)),
                    ItemKind::Func(_) => ComponentTypeRef::Func(ty),
                    ItemKind::Instance(_) => ComponentTypeRef::Instance(ty),
                    ItemKind::Component(_) => ComponentTypeRef::Component(ty),
                    ItemKind::Module(_) => ComponentTypeRef::Module(ty),
                    ItemKind::Value(_) => ComponentTypeRef::Value(ComponentValType::Type(ty)),
                },
            );

            let prev = encoded.insert(name, (kind.into(), index));
            assert!(prev.is_none());
        }

        // Finally populate the implicit argument map
        for (node, name) in arguments {
            let (kind, index) = encoded[name.as_str()];
            state
                .implicit_args
                .entry(node)
                .or_default()
                .push((name.clone(), kind, index));
        }

        Ok(())
    }

    fn definition(&self, state: &mut State, data: &NodeData<C>) -> u32 {
        let types = self.0.node_types(data);
        let name = data.export.as_deref().unwrap();

        log::debug!(
            "encoding definition `{name}` ({kind})",
            kind = data.item_kind.desc(types)
        );

        let encoder = TypeEncoder::new(types);
        let (ty, index) = match data.item_kind {
            ItemKind::Type(ty) => match ty {
                Type::Resource(_) => unreachable!("resources cannot be defined"),
                Type::Func(id) => (ty, encoder.ty(state, Type::Func(id), None)),
                Type::Value(id) => (ty, encoder.ty(state, Type::Value(id), None)),
                Type::Interface(id) => (ty, encoder.interface(state, id)),
                Type::World(id) => (ty, encoder.world(state, id)),
                Type::Module(id) => (ty, encoder.ty(state, Type::Module(id), None)),
            },
            _ => unreachable!("only types can be defined"),
        };

        let index = state
            .builder()
            .export(name, ComponentExportKind::Type, index, None);

        // Remap to the exported index
        state.current.type_indexes.insert(ty, index);

        log::debug!("definition `{name}` encoded to type index {index}");
        index
    }

    fn import(&self, state: &mut State, name: &str, data: &NodeData<C>) -> u32 {
        let types = self.0.node_types(data);

        log::debug!(
            "encoding import `{name}` ({kind})",
            kind = data.item_kind.desc(self.0.node_types(data))
        );

        let encoder = TypeEncoder::new(types);
        let ty = match data.item_kind {
            ItemKind::Type(ty) => {
                ComponentTypeRef::Type(TypeBounds::Eq(encoder.ty(state, ty, None)))
            }
            ItemKind::Func(id) => ComponentTypeRef::Func(encoder.ty(state, Type::Func(id), None)),
            ItemKind::Instance(id) => {
                // Check to see if the instance has already been imported
                // This may occur when an interface uses another
                if let Some(index) = state.current.instances.get(&id) {
                    log::debug!("skipping import of interface {id} as it was already imported with instance index {index}");
                    return *index;
                }

                ComponentTypeRef::Instance(encoder.ty(state, Type::Interface(id), None))
            }
            ItemKind::Component(id) => {
                ComponentTypeRef::Component(encoder.ty(state, Type::World(id), None))
            }
            ItemKind::Module(id) => {
                ComponentTypeRef::Module(encoder.ty(state, Type::Module(id), None))
            }
            ItemKind::Value(ty) => ComponentTypeRef::Value(encoder.value_type(state, ty)),
        };

        let index = state.builder().import(name, ty);
        log::debug!("import `{name}` encoded to {ty:?}");

        match data.item_kind {
            ItemKind::Type(ty) => {
                // Remap to the imported index
                state.current.type_indexes.insert(ty, index);
            }
            ItemKind::Instance(id) => {
                log::debug!("interface {id} is available for aliasing as instance index {index}");
                state.current.instances.insert(id, index);
            }
            _ => {}
        }

        index
    }

    fn instantiation(
        &self,
        state: &mut State,
        node: NodeId,
        data: &NodeData<C>,
        options: EncodeOptions,
    ) -> u32 {
        let package_id = data.package.expect("instantiation requires a package");
        let package = self.0.packages[package_id.index].package.as_ref().unwrap();
        let imports = &package.types()[package.ty()].imports;

        let component_index = if let Some(index) = state.packages.get(&package_id) {
            *index
        } else {
            let index = if options.define_components {
                state.builder().component_raw(package.bytes())
            } else {
                let encoder = TypeEncoder::new(package.types());
                let ty = encoder.component(state, package.ty());
                state.builder().import(
                    &Self::package_import_name(package),
                    ComponentTypeRef::Component(ty),
                )
            };

            state.packages.insert(package_id, index);
            index
        };

        let mut arguments = Vec::with_capacity(imports.len());
        arguments.extend(
            self.0
                .graph
                .edges_directed(node, Direction::Incoming)
                .flat_map(|(s, _, e)| {
                    let kind = self.0.node_data(s).item_kind.into();
                    let index = state.node_indexes[&s];
                    match e {
                        Edge::Alias(_) => unreachable!(),
                        Edge::Argument(i) => i.iter().map(move |i| {
                            (
                                Cow::Borrowed(imports.get_index(*i).unwrap().0.as_str()),
                                kind,
                                index,
                            )
                        }),
                    }
                }),
        );

        if let Some(implicit) = state.implicit_args.remove(&node) {
            arguments.extend(implicit.into_iter().map(|(n, k, i)| (n.into(), k, i)));
        }

        log::debug!(
            "instantiating package `{package}` with arguments: {arguments:?}",
            package = package.name(),
        );

        let index = state.builder().instantiate(component_index, arguments);

        log::debug!(
            "instantiation of package `{package}` encoded to instance index {index}",
            package = package.name(),
        );

        index
    }

    fn alias(&self, state: &mut State, node: NodeId, data: &NodeData<C>) -> u32 {
        let (source, export) = self
            .0
            .get_alias_source(node)
            .expect("alias should have a source");

        let source_data = self.0.node_data(source);
        let types = self.0.node_types(data);
        let exports = match source_data.item_kind {
            ItemKind::Instance(id) => &types[id].exports,
            _ => unreachable!(),
        };

        let kind = exports[export];
        let instance = state.node_indexes[&source];

        log::debug!(
            "encoding alias for export `{export}` ({kind}) of instance {instance}",
            kind = kind.desc(types),
        );

        let index = state.builder().alias(Alias::InstanceExport {
            instance,
            kind: kind.into(),
            name: export,
        });

        log::debug!("alias of export `{export}` encoded to index {index} ({kind:?})",);
        index
    }

    fn package_import_name(package: &Package) -> String {
        let mut name = String::new();

        write!(&mut name, "unlocked-dep=<{name}", name = package.name()).unwrap();
        if let Some(version) = package.version() {
            write!(&mut name, "@{{>={version}}}", version = version).unwrap();
        }

        write!(&mut name, ">").unwrap();
        name
    }

    fn encode_names(&self, state: &State, encoded: &mut ComponentBuilder) {
        let mut names = ComponentNameSection::new();
        let mut types = NameMap::new();
        let mut funcs = NameMap::new();
        let mut instances = NameMap::new();
        let mut components = NameMap::new();
        let mut modules = NameMap::new();
        let mut values = NameMap::new();

        for node in self.0.nodes() {
            let data = self.0.node_data(node);
            if let Some(name) = &data.name {
                let map = match data.item_kind {
                    ItemKind::Type(_) => &mut types,
                    ItemKind::Func(_) => &mut funcs,
                    ItemKind::Instance(_) => &mut instances,
                    ItemKind::Component(_) => &mut components,
                    ItemKind::Module(_) => &mut modules,
                    ItemKind::Value(_) => &mut values,
                };

                let index = state.node_indexes[&node];
                map.append(index, name)
            }
        }

        if !types.is_empty() {
            names.types(&types);
        }

        if !funcs.is_empty() {
            names.funcs(&funcs);
        }

        if !instances.is_empty() {
            names.instances(&instances);
        }

        if !components.is_empty() {
            names.components(&components);
        }

        if !modules.is_empty() {
            names.core_modules(&modules);
        }

        if !values.is_empty() {
            names.values(&values);
        }

        if !names.is_empty() {
            encoded.custom_section(&names.as_custom());
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use wac_types::{DefinedType, PrimitiveType, Resource, ValueType};

    #[test]
    fn it_errors_with_type_not_defined() {
        let mut graph = CompositionGraph::new();
        // Define the type in a different type collection
        let mut types = Types::new();
        let id = types.add_defined_type(DefinedType::Alias(ValueType::Primitive(
            PrimitiveType::Bool,
        )));
        assert!(matches!(
            graph
                .add_type_definition_node(
                    "foo",
                    Type::Value(ValueType::Defined {
                        id,
                        contains_borrow: false
                    }),
                    ()
                )
                .unwrap_err(),
            Error::TypeNotDefined { .. }
        ));
    }

    #[test]
    fn it_adds_a_type_definition() {
        let mut graph = CompositionGraph::new();
        let id = graph
            .types_mut()
            .add_defined_type(DefinedType::Alias(ValueType::Primitive(
                PrimitiveType::Bool,
            )));
        assert!(graph
            .add_type_definition_node(
                "foo",
                Type::Value(ValueType::Defined {
                    id,
                    contains_borrow: false
                }),
                ()
            )
            .is_ok());
    }

    #[test]
    fn it_cannot_define_a_resource() {
        let mut graph = CompositionGraph::new();
        let id = graph.types_mut().add_resource(Resource {
            name: "a".to_string(),
            alias_of: None,
        });
        assert!(matches!(
            graph
                .add_type_definition_node("foo", Type::Resource(id), ())
                .unwrap_err(),
            Error::CannotDefineResource
        ));
    }

    #[test]
    fn it_validates_package_ids() {
        let mut graph = CompositionGraph::new();
        let old = graph
            .register_package(
                Package::from_bytes("foo:bar", None, wat::parse_str("(component)").unwrap())
                    .unwrap(),
            )
            .unwrap();

        assert_eq!(old.index, 0);
        assert_eq!(old.generation, 0);

        graph.unregister_package(old).unwrap();

        let new = graph
            .register_package(
                Package::from_bytes("foo:bar", None, wat::parse_str("(component)").unwrap())
                    .unwrap(),
            )
            .unwrap();

        assert_eq!(new.index, 0);
        assert_eq!(new.generation, 1);

        assert!(matches!(
            graph.add_instantiation_node(old, ()).unwrap_err(),
            Error::InvalidPackageId,
        ));

        graph.add_instantiation_node(new, ()).unwrap();
    }

    #[test]
    fn it_validates_node_ids() {
        let mut graph = CompositionGraph::new();
        let pkg = graph
            .register_package(
                Package::from_bytes(
                    "foo:bar",
                    None,
                    wat::parse_str(r#"(component (import "foo" (func)) (export "foo" (func 0)))"#)
                        .unwrap(),
                )
                .unwrap(),
            )
            .unwrap();

        let old = graph.add_instantiation_node(pkg, ()).unwrap();
        assert_eq!(old.index, 0);
        assert_eq!(old.generation, 0);

        assert!(graph.remove_node(old));
        let new = graph.add_instantiation_node(pkg, ()).unwrap();
        assert_eq!(new.index, 0);
        assert_eq!(new.generation, 1);

        assert!(matches!(
            graph.add_alias_node(old, "foo", ()).unwrap_err(),
            Error::InvalidNodeId,
        ));

        graph.add_alias_node(new, "foo", ()).unwrap();
    }

    #[test]
    fn it_must_export_a_type_definition() {
        let mut graph = CompositionGraph::new();
        let id = graph
            .types_mut()
            .add_defined_type(DefinedType::Alias(ValueType::Primitive(PrimitiveType::S32)));
        let id = graph
            .add_type_definition_node(
                "foo",
                Type::Value(ValueType::Defined {
                    id,
                    contains_borrow: false,
                }),
                (),
            )
            .unwrap();
        assert!(matches!(
            graph.unexport_node(id).unwrap_err(),
            Error::MustExportDefinition
        ));
    }
}
