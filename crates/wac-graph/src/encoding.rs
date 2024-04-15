use crate::PackageId;
use indexmap::IndexMap;
use petgraph::graph::NodeIndex;
use std::collections::HashMap;
use wac_types::{
    CoreExtern, DefinedType, DefinedTypeId, Enum, Flags, FuncResult, FuncTypeId, InterfaceId,
    ItemKind, ModuleTypeId, PrimitiveType, Record, ResourceId, Type, Types, UsedType, ValueType,
    Variant, WorldId,
};
use wasm_encoder::{
    Alias, ComponentBuilder, ComponentExportKind, ComponentOuterAliasKind, ComponentType,
    ComponentTypeEncoder, ComponentTypeRef, ComponentValType, CoreTypeEncoder, EntityType,
    GlobalType, InstanceType, MemoryType, ModuleType, TableType, TagKind, TagType, TypeBounds,
};

/// A type used to abstract the API differences between a component builder,
/// component type, and instance type from `wasm-encoder`.
#[derive(Debug)]
enum Encodable {
    Builder(ComponentBuilder),
    Instance(InstanceType),
    Component(ComponentType),
}

impl Encodable {
    fn type_count(&self) -> u32 {
        match self {
            Encodable::Builder(t) => t.type_count(),
            Encodable::Component(t) => t.type_count(),
            Encodable::Instance(t) => t.type_count(),
        }
    }

    fn instance_count(&self) -> u32 {
        match self {
            Encodable::Builder(t) => t.instance_count(),
            Encodable::Component(t) => t.instance_count(),
            Encodable::Instance(t) => t.instance_count(),
        }
    }

    fn core_type_count(&self) -> u32 {
        match self {
            Encodable::Builder(t) => t.core_type_count(),
            Encodable::Component(t) => t.core_type_count(),
            Encodable::Instance(t) => t.core_type_count(),
        }
    }

    fn ty(&mut self) -> ComponentTypeEncoder {
        match self {
            Encodable::Builder(t) => t.ty().1,
            Encodable::Instance(t) => t.ty(),
            Encodable::Component(t) => t.ty(),
        }
    }

    fn core_type(&mut self) -> CoreTypeEncoder {
        match self {
            Encodable::Builder(t) => t.core_type().1,
            Encodable::Instance(t) => t.core_type(),
            Encodable::Component(t) => t.core_type(),
        }
    }

    fn import_type(&mut self, name: &str, ty: ComponentTypeRef) {
        match self {
            Encodable::Component(t) => {
                t.import(name, ty);
            }
            Encodable::Builder(b) => {
                b.import(name, ty);
            }
            _ => panic!("expected a component type"),
        }
    }

    fn alias(&mut self, alias: Alias) {
        match self {
            Encodable::Builder(t) => {
                t.alias(alias);
            }
            Encodable::Instance(t) => {
                t.alias(alias);
            }
            Encodable::Component(t) => {
                t.alias(alias);
            }
        }
    }
}

impl Default for Encodable {
    fn default() -> Self {
        Self::Builder(Default::default())
    }
}

#[derive(Debug, Default)]
pub struct Scope {
    /// The map from types to encoded type index.
    pub type_indexes: IndexMap<Type, u32>,
    /// The map from interface name (i.e. id) to encoded instance index.
    pub instances: IndexMap<String, u32>,
    /// The map of import/export name to their alias indexes.
    type_aliases: IndexMap<String, u32>,
    /// The map of resource names to their encoded indexes.
    resources: IndexMap<String, u32>,
    /// The encodable for this scope.
    encodable: Encodable,
}

#[derive(Debug, Default)]
pub struct State {
    /// The stack of encoding scopes.
    scopes: Vec<Scope>,
    /// The current encoding scope.
    pub current: Scope,
    /// A map of nodes in the graph to their encoded indexes.
    pub node_indexes: HashMap<NodeIndex, u32>,
    /// The map of package identifiers to encoded components (either imported or defined).
    pub packages: HashMap<PackageId, u32>,
    /// A map of instantiation nodes to a list of their encoded implicitly imported arguments.
    pub implicit_args: HashMap<NodeIndex, Vec<(String, ComponentExportKind, u32)>>,
}

impl State {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn builder(&mut self) -> &mut ComponentBuilder {
        assert!(self.scopes.is_empty(), "expected scopes to be empty");
        match &mut self.current.encodable {
            Encodable::Builder(builder) => builder,
            _ => panic!("expected a builder"),
        }
    }

    fn push(&mut self, encodable: Encodable) {
        log::debug!("pushing new type scope");
        let prev = std::mem::replace(
            &mut self.current,
            Scope {
                encodable,
                ..Default::default()
            },
        );

        self.scopes.push(prev);
    }

    fn pop(&mut self) -> Encodable {
        log::debug!("popping type scope");
        let prev = std::mem::replace(
            &mut self.current,
            self.scopes.pop().expect("expected a scope to pop"),
        );
        prev.encodable
    }

    fn used_type_index(&mut self, name: &str) -> Option<u32> {
        if let Some(index) = self.current.type_aliases.get(name) {
            return Some(*index);
        }

        if let Some(parent) = self.scopes.last() {
            if let Some(outer) = parent.type_aliases.get(name) {
                let index = self.current.encodable.type_count();
                log::debug!("encoding outer alias for `{name}` to type index {index}");
                self.current.encodable.alias(Alias::Outer {
                    kind: ComponentOuterAliasKind::Type,
                    count: 1,
                    index: *outer,
                });
                return Some(index);
            }
        }

        None
    }
}

pub struct TypeEncoder<'a>(&'a Types);

impl<'a> TypeEncoder<'a> {
    pub fn new(types: &'a Types) -> Self {
        Self(types)
    }

    pub fn ty(&self, state: &mut State, ty: Type, name: Option<&str>) -> u32 {
        if let Some(index) = state.current.type_indexes.get(&ty) {
            return *index;
        }

        if let Some(name) = name {
            if let Some(index) = state.used_type_index(name) {
                state.current.type_indexes.insert(ty, index);
                return index;
            }
        }

        let index = match ty {
            Type::Resource(_) => panic!("cannot encode a resource"),
            Type::Func(id) => self.func_type(state, id),
            Type::Value(ValueType::Primitive(ty)) => Self::primitive(state, ty),
            Type::Value(ValueType::Borrow(id)) => self.borrow(state, id),
            Type::Value(ValueType::Own(id)) => self.own(state, id),
            Type::Value(ValueType::Defined(id)) => self.defined(state, id),
            Type::Interface(id) => self.instance(state, id, false),
            Type::World(id) => self.component(state, id),
            Type::Module(id) => self.module(state, id),
        };

        state.current.type_indexes.insert(ty, index);
        index
    }

    fn func_type(&self, state: &mut State, id: FuncTypeId) -> u32 {
        log::debug!("encoding function type");
        let ty = &self.0[id];

        let params = ty
            .params
            .iter()
            .map(|(n, ty)| (n.as_str(), self.value_type(state, *ty)))
            .collect::<Vec<_>>();

        let results = match &ty.results {
            Some(FuncResult::Scalar(ty)) => vec![("", self.value_type(state, *ty))],
            Some(FuncResult::List(results)) => results
                .iter()
                .map(|(n, ty)| (n.as_str(), self.value_type(state, *ty)))
                .collect(),
            None => Vec::new(),
        };

        let index = state.current.encodable.type_count();
        let mut encoder = state.current.encodable.ty().function();
        encoder.params(params);

        match &ty.results {
            Some(FuncResult::Scalar(_)) => {
                encoder.result(results[0].1);
            }
            _ => {
                encoder.results(results);
            }
        }

        log::debug!("function type encoded to type index {index}");
        index
    }

    fn defined(&self, state: &mut State, id: DefinedTypeId) -> u32 {
        log::debug!("encoding defined type");
        let ty = &self.0[id];
        let index = match ty {
            DefinedType::Tuple(types) => self.tuple(state, types),
            DefinedType::List(ty) => self.list(state, *ty),
            DefinedType::Option(ty) => self.option(state, *ty),
            DefinedType::Result { ok, err } => self.result(state, *ok, *err),
            DefinedType::Variant(v) => self.variant(state, v),
            DefinedType::Record(r) => self.record(state, r),
            DefinedType::Flags(f) => self.flags(state, f),
            DefinedType::Enum(e) => self.enum_type(state, e),
            DefinedType::Alias(ValueType::Primitive(ty)) => Self::primitive(state, *ty),
            DefinedType::Alias(ValueType::Borrow(id)) => self.borrow(state, *id),
            DefinedType::Alias(ValueType::Own(id)) => self.own(state, *id),
            DefinedType::Alias(ValueType::Defined(id)) => self.defined(state, *id),
        };

        log::debug!("defined type encoded to type index {index}");
        index
    }

    fn use_aliases(&self, state: &mut State, uses: &'a IndexMap<String, UsedType>) {
        state.current.type_aliases.clear();

        for (name, used) in uses {
            let interface = &self.0[used.interface];
            let iid = interface.id.as_ref().expect("interface should have an id");
            let instance = state.current.instances[iid];
            let index = state.current.encodable.type_count();
            let export: &String = used.name.as_ref().unwrap_or(name);
            let kind = interface.exports.get(export).unwrap();
            state.current.encodable.alias(Alias::InstanceExport {
                instance,
                kind: ComponentExportKind::Type,
                name: export,
            });

            log::debug!(
                "aliased {kind} export `{export}` of instance index {instance} ({iid}) to type index {index}",
                kind = kind.desc(self.0)
            );

            state.current.type_aliases.insert(name.clone(), index);
        }
    }

    fn instance(&self, state: &mut State, id: InterfaceId, types_only: bool) -> u32 {
        log::debug!("encoding instance type");
        let interface = &self.0[id];
        for used in interface.uses.values() {
            self.import_deps(state, used.interface);
        }

        // Encode any required aliases
        self.use_aliases(state, &interface.uses);
        state.push(Encodable::Instance(InstanceType::default()));

        // Otherwise, export all exports
        for (name, kind) in &interface.exports {
            match kind {
                ItemKind::Type(_) => {
                    self.export(state, name, *kind);
                }
                _ => {
                    if !types_only {
                        self.export(state, name, *kind);
                    }
                }
            }
        }

        match state.pop() {
            Encodable::Instance(ty) => {
                let index = state.current.encodable.type_count();
                state.current.encodable.ty().instance(&ty);
                log::debug!("instance type encoded to type index {index}");
                index
            }
            _ => panic!("expected the pushed encodable to be an instance type"),
        }
    }

    pub fn component(&self, state: &mut State, id: WorldId) -> u32 {
        log::debug!("encoding component type");
        let world = &self.0[id];

        state.push(Encodable::Component(ComponentType::default()));

        for used in world.uses.values() {
            self.import_deps(state, used.interface);
        }

        self.use_aliases(state, &world.uses);

        for (name, kind) in &world.imports {
            self.import(state, name, *kind);
        }

        for (name, kind) in &world.exports {
            self.export(state, name, *kind);
        }

        match state.pop() {
            Encodable::Component(ty) => {
                let index = state.current.encodable.type_count();
                state.current.encodable.ty().component(&ty);
                log::debug!("component type encoded to type index {index}");
                index
            }
            _ => panic!("expected the pushed encodable to be a component type"),
        }
    }

    fn import_deps(&self, state: &mut State, id: InterfaceId) {
        let iid = self.0[id].id.as_ref().expect("interface should have an id");
        if state.current.instances.contains_key(iid) {
            return;
        }

        let interface = &self.0[id];

        // Depth-first recurse on the dependencies of this interface
        for used in interface.uses.values() {
            self.import_deps(state, used.interface);
        }

        log::debug!("encoding dependency on interface `{iid}`");

        let index = self.instance(state, id, !state.scopes.is_empty());
        let import_index = state.current.encodable.instance_count();

        state
            .current
            .encodable
            .import_type(iid, ComponentTypeRef::Instance(index));

        log::debug!(
            "interface `{iid}` is available for aliasing from instance index {import_index}"
        );
        state.current.instances.insert(iid.clone(), import_index);
    }

    pub fn interface(&self, state: &mut State, id: InterfaceId) -> u32 {
        let interface = &self.0[id];
        let iid = interface.id.as_deref().expect("interface must have an id");
        log::debug!("encoding interface definition of `{iid}`");
        assert!(state.scopes.is_empty());
        state.push(Encodable::Component(ComponentType::default()));

        for used in interface.uses.values() {
            self.import_deps(state, used.interface);
        }

        let index = self.instance(state, id, false);
        Self::export_type(state, iid, ComponentTypeRef::Instance(index));

        match state.pop() {
            Encodable::Component(ty) => {
                let (index, encoder) = state.builder().ty();
                encoder.component(&ty);
                log::debug!("encoded interface definition of `{iid}` to type index {index}",);
                index
            }
            _ => panic!("expected the pushed encodable to be a component type"),
        }
    }

    pub fn world(&self, state: &mut State, id: WorldId) -> u32 {
        let world = &self.0[id];
        let world_id = world.id.as_deref().expect("world must have an id");
        log::debug!("encoding world definition of `{world_id}`");

        assert!(state.scopes.is_empty());
        state.push(Encodable::Component(ComponentType::default()));
        let index = self.component(state, id);
        Self::export_type(state, world_id, ComponentTypeRef::Component(index));

        match state.pop() {
            Encodable::Component(ty) => {
                let (index, encoder) = state.builder().ty();
                encoder.component(&ty);
                log::debug!("encoded world definition of `{world_id}` to type index {index}");
                index
            }
            _ => panic!("expected the push encodable to be a component type"),
        }
    }

    fn module(&self, state: &mut State, id: ModuleTypeId) -> u32 {
        log::debug!("encoding module definition");
        let ty = &self.0[id];
        let mut encoded = ModuleType::new();

        for ((module, name), ext) in &ty.imports {
            let ty = self.entity_type(&mut encoded, ext);
            encoded.import(module, name, ty);
        }

        for (name, ext) in &ty.exports {
            let ty = self.entity_type(&mut encoded, ext);
            encoded.export(name, ty);
        }

        let index = state.current.encodable.core_type_count();
        state.current.encodable.core_type().module(&encoded);
        log::debug!("encoded module definition to type index {index}");
        index
    }

    fn entity_type(&self, encodable: &mut ModuleType, ext: &CoreExtern) -> EntityType {
        match ext {
            CoreExtern::Func(func) => {
                let index = encodable.type_count();
                encodable.ty().function(
                    func.params.iter().copied().map(Into::into),
                    func.results.iter().copied().map(Into::into),
                );
                EntityType::Function(index)
            }
            CoreExtern::Table {
                element_type,
                initial,
                maximum,
            } => EntityType::Table(TableType {
                element_type: (*element_type).into(),
                minimum: *initial,
                maximum: *maximum,
            }),
            CoreExtern::Memory {
                memory64,
                shared,
                initial,
                maximum,
            } => EntityType::Memory(MemoryType {
                minimum: *initial,
                maximum: *maximum,
                memory64: *memory64,
                shared: *shared,
            }),
            CoreExtern::Global { val_type, mutable } => EntityType::Global(GlobalType {
                val_type: (*val_type).into(),
                mutable: *mutable,
            }),
            CoreExtern::Tag(func) => {
                let index = encodable.type_count();
                encodable.ty().function(
                    func.params.iter().copied().map(Into::into),
                    func.results.iter().copied().map(Into::into),
                );
                EntityType::Tag(TagType {
                    kind: TagKind::Exception,
                    func_type_idx: index,
                })
            }
        }
    }

    pub fn value_type(&self, state: &mut State, ty: ValueType) -> ComponentValType {
        if let Some(index) = state.current.type_indexes.get(&Type::Value(ty)) {
            return ComponentValType::Type(*index);
        }

        let index = match ty {
            ValueType::Primitive(ty) => return ComponentValType::Primitive(ty.into()),
            ValueType::Borrow(id) => self.borrow(state, id),
            ValueType::Own(id) => self.own(state, id),
            ValueType::Defined(id) => self.defined(state, id),
        };

        state.current.type_indexes.insert(Type::Value(ty), index);
        ComponentValType::Type(index)
    }

    fn primitive(state: &mut State, ty: PrimitiveType) -> u32 {
        let index = state.current.encodable.type_count();
        state
            .current
            .encodable
            .ty()
            .defined_type()
            .primitive(ty.into());
        index
    }

    fn tuple(&self, state: &mut State, types: &[ValueType]) -> u32 {
        let types = types
            .iter()
            .map(|ty| self.value_type(state, *ty))
            .collect::<Vec<_>>();
        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().tuple(types);
        index
    }

    fn list(&self, state: &mut State, ty: ValueType) -> u32 {
        let ty = self.value_type(state, ty);
        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().list(ty);
        index
    }

    fn option(&self, state: &mut State, ty: ValueType) -> u32 {
        let ty = self.value_type(state, ty);
        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().option(ty);
        index
    }

    fn result(&self, state: &mut State, ok: Option<ValueType>, err: Option<ValueType>) -> u32 {
        let ok = ok.map(|ty| self.value_type(state, ty));
        let err = err.map(|ty| self.value_type(state, ty));
        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().result(ok, err);
        index
    }

    fn borrow(&self, state: &mut State, res: ResourceId) -> u32 {
        assert!(!state.scopes.is_empty());
        let res = state.current.resources[self.0[res].name.as_str()];
        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().borrow(res);
        index
    }

    fn own(&self, state: &mut State, res: ResourceId) -> u32 {
        let res = state.current.resources[self.0[res].name.as_str()];
        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().own(res);
        index
    }

    fn variant(&self, state: &mut State, variant: &Variant) -> u32 {
        let cases = variant
            .cases
            .iter()
            .map(|(n, ty)| (n.as_str(), ty.map(|ty| self.value_type(state, ty)), None))
            .collect::<Vec<_>>();

        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().variant(cases);
        index
    }

    fn record(&self, state: &mut State, record: &Record) -> u32 {
        let fields = record
            .fields
            .iter()
            .map(|(n, ty)| (n.as_str(), self.value_type(state, *ty)))
            .collect::<Vec<_>>();
        let index = state.current.encodable.type_count();
        state.current.encodable.ty().defined_type().record(fields);
        index
    }

    fn flags(&self, state: &mut State, flags: &Flags) -> u32 {
        let index = state.current.encodable.type_count();
        state
            .current
            .encodable
            .ty()
            .defined_type()
            .flags(flags.0.iter().map(String::as_str));
        index
    }

    fn enum_type(&self, state: &mut State, e: &Enum) -> u32 {
        let index = state.current.encodable.type_count();
        state
            .current
            .encodable
            .ty()
            .defined_type()
            .enum_type(e.0.iter().map(String::as_str));
        index
    }

    fn import(&self, state: &mut State, name: &str, kind: ItemKind) {
        if let ItemKind::Type(Type::Resource(id)) = kind {
            self.import_resource(state, name, id);
            return;
        }

        log::debug!("encoding {kind} import `{name}`", kind = kind.desc(self.0));
        let ty = kind.ty();
        let index = self.ty(state, ty, Some(name));

        match kind {
            ItemKind::Type(_) => {
                let import_index = state.current.encodable.type_count();
                state
                    .current
                    .encodable
                    .import_type(name, ComponentTypeRef::Type(TypeBounds::Eq(index)));

                // Remap the type to the index of the imported item
                state.current.type_indexes.insert(ty, import_index);
            }
            ItemKind::Func(_) => {
                state
                    .current
                    .encodable
                    .import_type(name, ComponentTypeRef::Func(index));
            }
            ItemKind::Instance(id) => {
                let import_index = state.current.encodable.instance_count();
                state
                    .current
                    .encodable
                    .import_type(name, ComponentTypeRef::Instance(index));
                if let Some(iid) = &self.0[id].id {
                    log::debug!("instance index {import_index} ({iid}) is available for aliasing");
                    state.current.instances.insert(iid.clone(), import_index);
                }
            }
            _ => panic!("expected only types, functions, and instance types"),
        }
    }

    pub fn import_resource(&self, state: &mut State, name: &str, id: ResourceId) -> u32 {
        if let Some(index) = state.current.resources.get(name) {
            return *index;
        }

        log::debug!("encoding import of resource `{name}`");

        let resource = &self.0[id];
        let index = if let Some(outer) = state.used_type_index(name) {
            // This is an alias to an outer resource type
            let index = state.current.encodable.type_count();
            state
                .current
                .encodable
                .import_type(name, ComponentTypeRef::Type(TypeBounds::Eq(outer)));

            log::debug!("encoded outer alias for resource `{name}` to type index {index}");
            index
        } else if let Some(alias) = resource.alias {
            let source = self.0.resolve_resource(alias.source);
            let source_index = if let Some(index) =
                state.current.resources.get(self.0[source].name.as_str())
            {
                // The source resource was previously imported
                *index
            } else if let Some(index) = state.current.type_indexes.get(&Type::Resource(source)) {
                // The source resource isn't directly imported, but was previously aliased
                *index
            } else {
                // Otherwise, we need to alias the source resource
                // This should only occur for resources owned by interfaces
                let source_index = state.current.encodable.type_count();
                let iid = self.0[alias.owner.expect("should have owner")]
                    .id
                    .as_deref()
                    .expect("expected an interface with an id");
                state.current.encodable.alias(Alias::InstanceExport {
                    instance: state.current.instances[iid],
                    kind: ComponentExportKind::Type,
                    name: self.0[source].name.as_str(),
                });
                state
                    .current
                    .type_indexes
                    .insert(Type::Resource(source), source_index);
                source_index
            };

            let index = state.current.encodable.type_count();
            state
                .current
                .encodable
                .import_type(name, ComponentTypeRef::Type(TypeBounds::Eq(source_index)));

            log::debug!("encoded import for resource `{name}` as type index {index} (alias of type index {source_index})");
            index
        } else {
            // Otherwise, this is a new resource type, import with a subtype bounds
            let index = state.current.encodable.type_count();
            state
                .current
                .encodable
                .import_type(name, ComponentTypeRef::Type(TypeBounds::SubResource));

            log::debug!("encoded import for resource `{name}` to type index {index}");
            index
        };

        state.current.resources.insert(resource.name.clone(), index);
        index
    }

    fn export(&self, state: &mut State, name: &str, kind: ItemKind) -> u32 {
        if let ItemKind::Type(Type::Resource(id)) = kind {
            return self.export_resource(state, name, id);
        }

        log::debug!(
            "encoding {kind} export of `{name}`",
            kind = kind.desc(self.0)
        );

        let ty = kind.ty();
        let index = self.ty(state, ty, Some(name));
        let index = Self::export_type(
            state,
            name,
            match kind {
                ItemKind::Type(_) => ComponentTypeRef::Type(TypeBounds::Eq(index)),
                ItemKind::Func(_) => ComponentTypeRef::Func(index),
                ItemKind::Instance(_) => ComponentTypeRef::Instance(index),
                _ => panic!("expected only types, functions, and instance types"),
            },
        );

        // For types, remap to the index of the exported item
        if let ItemKind::Type(ty) = kind {
            state.current.type_indexes.insert(ty, index);
        }

        index
    }

    fn export_resource(&self, state: &mut State, name: &str, id: ResourceId) -> u32 {
        log::debug!("encoding export of resource `{name}`");

        if let Some(existing) = state.current.resources.get(name) {
            return *existing;
        }

        let resource = &self.0[id];
        let index = if let Some(outer) = state.used_type_index(name) {
            // This is an alias to an outer resource type
            let index =
                Self::export_type(state, name, ComponentTypeRef::Type(TypeBounds::Eq(outer)));
            log::debug!("encoded outer alias for resource `{name}` as type index {index}");
            index
        } else if let Some(alias) = resource.alias {
            // This is an alias to another resource at the same scope
            let index = state.current.resources
                [self.0[self.0.resolve_resource(alias.source)].name.as_str()];
            let index =
                Self::export_type(state, name, ComponentTypeRef::Type(TypeBounds::Eq(index)));
            log::debug!("encoded alias for resource `{name}` as type index {index}");
            index
        } else {
            // Otherwise, this is a new resource type, export with a subtype bounds
            let index =
                Self::export_type(state, name, ComponentTypeRef::Type(TypeBounds::SubResource));
            log::debug!("encoded export of resource `{name}` as type index {index}");
            index
        };

        state.current.resources.insert(resource.name.clone(), index);
        index
    }

    fn export_type(state: &mut State, name: &str, ty: ComponentTypeRef) -> u32 {
        match &mut state.current.encodable {
            Encodable::Component(t) => {
                let index = t.type_count();
                t.export(name, ty);
                index
            }
            Encodable::Instance(t) => {
                let index = t.type_count();
                t.export(name, ty);
                index
            }
            Encodable::Builder(_) => panic!("expected a component or instance type"),
        }
    }
}
