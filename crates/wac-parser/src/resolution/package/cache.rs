//! This module contains the (convoluted) logic for caching package type
//! information.
//!
//! The cache serves as a deduplication mechanism for wasmparser types.
//!
//! For example, WIT duplicates interface definitions within any referring
//! world definition. This means that the same interface definition may
//! appear many times in a package. The cache allows us to deduplicate
//! these definitions so that they hash and compare equal based on their
//! structure.
//!
//! There are four main types defined in this module:
//!
//! - `ResourceMapper` - a utility type that scans import and export entities
//!   for resource definitions that can be deduplicated.
//! - `TypeHasher` - a utility type that can calculate a 64-bit hash value for
//!   a wasmparser type based on its structure.
//! - `TypeComparer` - a utility type that can compare two wasmparser types for
//!   structural equality.
//! - `TypeCache` - the main cache type that uses the above utilities to cache
//!   converted wasmparser types.
//!
//! The wasmparser type information needs to be shared between the above types.
//!
//! Additionally, some of the shared data structures need interior mutability
//! via `RefCell`.

use std::{
    cell::RefCell,
    collections::{hash_map::DefaultHasher, HashMap},
    fmt,
    hash::{Hash, Hasher},
    rc::Rc,
};
use wasmparser::{
    types::{
        ComponentDefinedType, ComponentEntityType, ComponentFuncType, ComponentInstanceType,
        ComponentType, ComponentValType, EntityType, ModuleType, ResourceId, Type, TypeId, Types,
    },
    PrimitiveValType,
};

/// Map between two type ids and the result of a comparison check.
type TypeComparisonMap = HashMap<(TypeId, TypeId), bool>;

/// Map between a type id and its structural hash.
type TypeHashMap = HashMap<TypeId, u64>;

/// Represents a mapped resource id.
///
/// This is used to deduplicate wasmparser resource ids so that
/// the same exported resource from an interface hashes and compares
/// equal.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct MappedResourceId(usize);

/// A map from wasmparser resource ids to internal resource ids.
pub type ResourceMap = HashMap<ResourceId, MappedResourceId>;

/// Represents a mapper of wasmparser resource ids to internal ids.
///
/// This allows the same exported resource from an interface to hash
/// and compare equal despite different wasmparser resource ids.
pub struct ResourceMapper {
    types: Rc<Types>,
    map: Rc<RefCell<ResourceMap>>,
    /// Map of qualified resource names (e.g. `foo:bar/baz/resource`) to mapped ids.
    resources: HashMap<String, MappedResourceId>,
    next_id: usize,
}

impl ResourceMapper {
    pub fn new(types: Rc<Types>) -> Self {
        Self {
            types,
            map: Default::default(),
            resources: Default::default(),
            next_id: 0,
        }
    }

    pub fn map(&self) -> Rc<RefCell<ResourceMap>> {
        self.map.clone()
    }

    pub fn get(&self, id: ResourceId) -> Option<MappedResourceId> {
        self.map.borrow().get(&id).copied()
    }

    pub fn component_entity_type(&mut self, name: &str, ty: ComponentEntityType) {
        let types = self.types.clone();

        match ty {
            ComponentEntityType::Module(_)
            | ComponentEntityType::Func(_)
            | ComponentEntityType::Value(_) => {}
            ComponentEntityType::Type { referenced, .. } => match &types[referenced] {
                Type::ComponentInstance(ty) => self.component_instance_type(name, ty),
                Type::Component(ty) => self.component_type(name, ty),
                _ => {}
            },
            ComponentEntityType::Instance(ty) => {
                self.component_instance_type(name, types[ty].unwrap_component_instance())
            }
            ComponentEntityType::Component(ty) => {
                self.component_type(name, types[ty].unwrap_component())
            }
        }
    }

    fn component_instance_type(&mut self, name: &str, ty: &ComponentInstanceType) {
        for (export, ty) in &ty.exports {
            if let ComponentEntityType::Type { referenced, .. } = ty {
                self.map_resource(name, export, *referenced);
            } else {
                self.component_entity_type(export, *ty);
            }
        }
    }

    fn component_type(&mut self, name: &str, ty: &ComponentType) {
        for (import, ty) in &ty.imports {
            if let ComponentEntityType::Type { referenced, .. } = ty {
                self.map_resource(name, import, *referenced);
            } else {
                self.component_entity_type(import, *ty);
            }
        }

        for (export, ty) in &ty.exports {
            self.component_entity_type(export, *ty);
        }
    }

    fn map_resource(&mut self, pkg: &str, name: &str, ty: TypeId) {
        let ty = self.resolve_alias(ty);
        if let Type::Resource(id) = self.types[ty] {
            self.map.borrow_mut().entry(id).or_insert_with(|| {
                *self
                    .resources
                    .entry(format!("{pkg}/{name}"))
                    .or_insert_with(|| {
                        let id = self.next_id;
                        self.next_id += 1;
                        MappedResourceId(id)
                    })
            });
        }
    }

    fn resolve_alias(&self, id: TypeId) -> TypeId {
        let mut cur = id;
        loop {
            cur = match self.types.peel_alias(cur) {
                Some(next) => next,
                None => break,
            };
        }
        cur
    }
}

/// Represents a wasmparser type hasher.
///
/// This is used to hash a wasmparser `TypeId` based on its structure.
struct TypeHasher<'a, H: Hasher> {
    types: &'a Types,
    resources: &'a ResourceMap,
    state: &'a mut H,
}

impl<'a, H: Hasher> TypeHasher<'a, H> {
    fn type_id(&mut self, ty: TypeId) {
        match self.types.get(ty).unwrap() {
            Type::Sub(_) => unreachable!("GC types are not a valid component extern type"),
            Type::Module(ty) => {
                1u8.hash(self.state);
                self.module_type(ty);
            }
            Type::Instance(_) => {
                unreachable!("module instances are not a valid component extern type")
            }
            Type::Component(ty) => {
                3u8.hash(self.state);
                self.component_type(ty);
            }
            Type::ComponentInstance(ty) => {
                4u8.hash(self.state);
                self.component_instance_type(ty)
            }
            Type::ComponentFunc(ty) => {
                5u8.hash(self.state);
                self.component_func_type(ty);
            }
            Type::Defined(ty) => {
                6u8.hash(self.state);
                self.component_defined_type(ty);
            }
            Type::Resource(id) => {
                7u8.hash(self.state);
                self.resources[id].hash(self.state);
            }
        }
    }

    fn module_type(&mut self, ty: &ModuleType) {
        ty.imports.len().hash(self.state);
        for (n, ty) in &ty.imports {
            n.hash(self.state);
            self.entity_type(*ty);
        }

        ty.exports.len().hash(self.state);
        for (n, ty) in &ty.exports {
            n.hash(self.state);
            self.entity_type(*ty);
        }
    }

    fn entity_type(&mut self, ty: EntityType) {
        match ty {
            EntityType::Func(ty) => {
                0u8.hash(self.state);
                self.type_id(ty);
            }
            EntityType::Table(ty) => (1u8, ty).hash(self.state),
            EntityType::Memory(ty) => (2u8, ty).hash(self.state),
            EntityType::Global(ty) => (3u8, ty).hash(self.state),
            EntityType::Tag(ty) => {
                4u8.hash(self.state);
                self.type_id(ty);
            }
        }
    }

    fn component_instance_type(&mut self, ty: &ComponentInstanceType) {
        ty.exports.len().hash(self.state);
        for (n, ty) in &ty.exports {
            n.hash(self.state);
            self.component_entity_type(ty);
        }
    }

    fn component_entity_type(&mut self, ty: &ComponentEntityType) {
        match ty {
            ComponentEntityType::Module(ty) => {
                0u8.hash(self.state);
                self.type_id(*ty);
            }
            ComponentEntityType::Func(ty) => {
                1u8.hash(self.state);
                self.type_id(*ty);
            }
            ComponentEntityType::Value(ty) => {
                2u8.hash(self.state);
                self.component_val_type(*ty);
            }
            ComponentEntityType::Type {
                referenced,
                created,
            } => {
                3u8.hash(self.state);
                self.type_id(*referenced);
                self.type_id(*created);
            }
            ComponentEntityType::Instance(ty) => {
                4u8.hash(self.state);
                self.type_id(*ty);
            }
            ComponentEntityType::Component(ty) => {
                5u8.hash(self.state);
                self.type_id(*ty);
            }
        }
    }

    fn component_val_type(&mut self, ty: ComponentValType) {
        match ty {
            ComponentValType::Primitive(ty) => {
                0u8.hash(self.state);
                self.primitive_val_type(ty);
            }
            ComponentValType::Type(ty) => {
                1u8.hash(self.state);
                self.type_id(ty);
            }
        }
    }

    fn primitive_val_type(&mut self, ty: PrimitiveValType) {
        match ty {
            PrimitiveValType::Bool => 0u8,
            PrimitiveValType::S8 => 1u8,
            PrimitiveValType::U8 => 2u8,
            PrimitiveValType::S16 => 3u8,
            PrimitiveValType::U16 => 4u8,
            PrimitiveValType::S32 => 5u8,
            PrimitiveValType::U32 => 6u8,
            PrimitiveValType::S64 => 7u8,
            PrimitiveValType::U64 => 8u8,
            PrimitiveValType::Float32 => 9u8,
            PrimitiveValType::Float64 => 10u8,
            PrimitiveValType::Char => 11u8,
            PrimitiveValType::String => 12u8,
        }
        .hash(self.state);
    }

    fn component_type(&mut self, ty: &ComponentType) {
        ty.imports.len().hash(self.state);
        for (n, ty) in &ty.imports {
            n.hash(self.state);
            self.component_entity_type(ty);
        }

        ty.exports.len().hash(self.state);
        for (n, ty) in &ty.exports {
            n.hash(self.state);
            self.component_entity_type(ty);
        }
    }

    fn component_func_type(&mut self, ty: &ComponentFuncType) {
        ty.params.len().hash(self.state);
        for (n, ty) in ty.params.iter() {
            n.hash(self.state);
            self.component_val_type(*ty);
        }

        ty.results.len().hash(self.state);
        for (n, ty) in ty.results.iter() {
            n.hash(self.state);
            self.component_val_type(*ty);
        }
    }

    fn component_defined_type(&mut self, ty: &ComponentDefinedType) {
        match ty {
            ComponentDefinedType::Primitive(ty) => {
                0u8.hash(self.state);
                self.primitive_val_type(*ty);
            }
            ComponentDefinedType::Record(r) => {
                1u8.hash(self.state);
                r.fields.len().hash(self.state);
                for (n, ty) in r.fields.iter() {
                    n.hash(self.state);
                    self.component_val_type(*ty);
                }
            }
            ComponentDefinedType::Variant(v) => {
                2u8.hash(self.state);
                v.cases.len().hash(self.state);
                for (n, case) in v.cases.iter() {
                    n.hash(self.state);
                    match case.ty {
                        Some(ty) => {
                            0u8.hash(self.state);
                            self.component_val_type(ty);
                        }
                        None => 1u8.hash(self.state),
                    }
                }
            }
            ComponentDefinedType::List(ty) => {
                3u8.hash(self.state);
                self.component_val_type(*ty);
            }
            ComponentDefinedType::Tuple(t) => {
                4u8.hash(self.state);
                t.types.len().hash(self.state);
                for ty in t.types.iter().copied() {
                    self.component_val_type(ty);
                }
            }
            ComponentDefinedType::Flags(flags) => {
                5u8.hash(self.state);
                flags.as_slice().hash(self.state);
            }
            ComponentDefinedType::Enum(cases) => {
                6u8.hash(self.state);
                cases.as_slice().hash(self.state);
            }
            ComponentDefinedType::Option(ty) => {
                7u8.hash(self.state);
                self.component_val_type(*ty);
            }
            ComponentDefinedType::Result { ok, err } => {
                8u8.hash(self.state);
                match ok {
                    Some(ty) => {
                        0u8.hash(self.state);
                        self.component_val_type(*ty);
                    }
                    None => 1u8.hash(self.state),
                }
                match err {
                    Some(ty) => {
                        0u8.hash(self.state);
                        self.component_val_type(*ty);
                    }
                    None => 1u8.hash(self.state),
                }
            }
            ComponentDefinedType::Own(ty) => {
                9u8.hash(self.state);
                self.type_id(*ty);
            }
            ComponentDefinedType::Borrow(ty) => {
                10u8.hash(self.state);
                self.type_id(*ty);
            }
        }
    }
}

/// Represents a type equality comparer.
///
/// It compares two wasmparser `TypeId` for _structural_ equality.
///
/// The result of any comparison is cached in the `comparisons` map.
struct TypeComparer<'a> {
    types: &'a Types,
    comparisons: &'a mut TypeComparisonMap,
    resources: &'a ResourceMap,
}

impl<'a> TypeComparer<'a> {
    fn type_id(&mut self, a: TypeId, b: TypeId) -> bool {
        // Check for id equality first
        if a == b {
            return true;
        }

        // Symmetrically check for a cached result
        if let Some(result) = self
            .comparisons
            .get(&(a, b))
            .or_else(|| self.comparisons.get(&(b, a)))
        {
            return *result;
        }

        // Otherwise, check for type structural equality
        let result = match (self.types.get(a).unwrap(), self.types.get(b).unwrap()) {
            (Type::Sub(_), Type::Sub(_)) => {
                unreachable!("GC types are not a valid component extern type")
            }
            (Type::Module(a), Type::Module(b)) => self.module_type(a, b),
            (Type::Instance(_), Type::Instance(_)) => {
                unreachable!("module instances are not a valid component extern type")
            }
            (Type::Component(a), Type::Component(b)) => self.component_type(a, b),
            (Type::ComponentInstance(a), Type::ComponentInstance(b)) => {
                self.component_instance_type(a, b)
            }
            (Type::ComponentFunc(a), Type::ComponentFunc(b)) => self.component_func_type(a, b),
            (Type::Defined(a), Type::Defined(b)) => self.component_defined_type(a, b),
            (Type::Resource(a), Type::Resource(b)) => {
                a == b || self.resources[a] == self.resources[b]
            }
            _ => false,
        };

        self.comparisons.insert((a, b), result);
        result
    }

    fn module_type(&mut self, a: &ModuleType, b: &ModuleType) -> bool {
        if a.imports.len() != b.imports.len() || a.exports.len() != b.exports.len() {
            return false;
        }

        a.imports
            .iter()
            .zip(b.imports.iter())
            .all(|((name_a, a), (name_b, b))| name_a == name_b && self.entity_type(*a, *b))
            && a.exports
                .iter()
                .zip(b.exports.iter())
                .all(|((name_a, a), (name_b, b))| name_a == name_b && self.entity_type(*a, *b))
    }

    fn entity_type(&mut self, a: EntityType, b: EntityType) -> bool {
        match (a, b) {
            (EntityType::Func(a), EntityType::Func(b)) => self.type_id(a, b),
            (EntityType::Table(a), EntityType::Table(b)) => a == b,
            (EntityType::Memory(a), EntityType::Memory(b)) => a == b,
            (EntityType::Global(a), EntityType::Global(b)) => a == b,
            (EntityType::Tag(a), EntityType::Tag(b)) => self.type_id(a, b),
            _ => false,
        }
    }

    fn component_type(&mut self, a: &ComponentType, b: &ComponentType) -> bool {
        if a.imports.len() != b.imports.len() || a.exports.len() != b.exports.len() {
            return false;
        }

        a.imports
            .iter()
            .zip(b.imports.iter())
            .all(|((name_a, a), (name_b, b))| {
                name_a == name_b && self.component_entity_type(*a, *b)
            })
            && a.exports
                .iter()
                .zip(b.exports.iter())
                .all(|((name_a, a), (name_b, b))| {
                    name_a == name_b && self.component_entity_type(*a, *b)
                })
    }

    fn component_entity_type(&mut self, a: ComponentEntityType, b: ComponentEntityType) -> bool {
        match (a, b) {
            (ComponentEntityType::Module(a), ComponentEntityType::Module(b)) => self.type_id(a, b),
            (ComponentEntityType::Func(a), ComponentEntityType::Func(b)) => self.type_id(a, b),
            (ComponentEntityType::Value(a), ComponentEntityType::Value(b)) => {
                self.component_val_type(a, b)
            }
            (
                ComponentEntityType::Type { referenced: a, .. },
                ComponentEntityType::Type { referenced: b, .. },
            ) => self.type_id(a, b),
            (ComponentEntityType::Instance(a), ComponentEntityType::Instance(b)) => {
                self.type_id(a, b)
            }
            (ComponentEntityType::Component(a), ComponentEntityType::Component(b)) => {
                self.type_id(a, b)
            }
            _ => false,
        }
    }

    fn component_val_type(&mut self, a: ComponentValType, b: ComponentValType) -> bool {
        match (a, b) {
            (ComponentValType::Primitive(a), ComponentValType::Primitive(b)) => a == b,
            (ComponentValType::Type(a), ComponentValType::Type(b)) => self.type_id(a, b),
            _ => false,
        }
    }

    fn component_instance_type(
        &mut self,
        a: &ComponentInstanceType,
        b: &ComponentInstanceType,
    ) -> bool {
        if a.exports.len() != b.exports.len() {
            return false;
        }

        a.exports
            .iter()
            .zip(b.exports.iter())
            .all(|((name_a, a), (name_b, b))| {
                name_a == name_b && self.component_entity_type(*a, *b)
            })
    }

    fn component_func_type(&mut self, a: &ComponentFuncType, b: &ComponentFuncType) -> bool {
        if a.params.len() != b.params.len() || a.results.len() != b.results.len() {
            return false;
        }

        a.params
            .iter()
            .zip(b.params.iter())
            .all(|((name_a, a), (name_b, b))| name_a == name_b && self.component_val_type(*a, *b))
            && a.results
                .iter()
                .zip(b.results.iter())
                .all(|((name_a, a), (name_b, b))| {
                    name_a == name_b && self.component_val_type(*a, *b)
                })
    }

    fn component_defined_type(
        &mut self,
        a: &ComponentDefinedType,
        b: &ComponentDefinedType,
    ) -> bool {
        match (a, b) {
            (ComponentDefinedType::Primitive(a), ComponentDefinedType::Primitive(b)) => a == b,
            (ComponentDefinedType::Record(a), ComponentDefinedType::Record(b)) => {
                if a.fields.len() != b.fields.len() {
                    return false;
                }

                a.fields
                    .iter()
                    .zip(b.fields.iter())
                    .all(|((name_a, a), (name_b, b))| {
                        name_a == name_b && self.component_val_type(*a, *b)
                    })
            }
            (ComponentDefinedType::Variant(a), ComponentDefinedType::Variant(b)) => {
                if a.cases.len() != b.cases.len() {
                    return false;
                }

                a.cases
                    .iter()
                    .zip(b.cases.iter())
                    .all(|((name_a, a), (name_b, b))| {
                        name_a == name_b
                            && match (a.ty, b.ty) {
                                (Some(a), Some(b)) => self.component_val_type(a, b),
                                (None, None) => true,
                                _ => false,
                            }
                    })
            }
            (ComponentDefinedType::List(a), ComponentDefinedType::List(b)) => {
                self.component_val_type(*a, *b)
            }
            (ComponentDefinedType::Tuple(a), ComponentDefinedType::Tuple(b)) => {
                if a.types.len() != b.types.len() {
                    return false;
                }

                a.types
                    .iter()
                    .zip(b.types.iter())
                    .all(|(a, b)| self.component_val_type(*a, *b))
            }
            (ComponentDefinedType::Flags(a), ComponentDefinedType::Flags(b)) => a == b,
            (ComponentDefinedType::Enum(a), ComponentDefinedType::Enum(b)) => a == b,
            (ComponentDefinedType::Option(a), ComponentDefinedType::Option(b)) => {
                self.component_val_type(*a, *b)
            }
            (
                ComponentDefinedType::Result {
                    ok: ok_a,
                    err: err_a,
                },
                ComponentDefinedType::Result {
                    ok: ok_b,
                    err: err_b,
                },
            ) => {
                match (ok_a, ok_b) {
                    (Some(a), Some(b)) => {
                        if !self.component_val_type(*a, *b) {
                            return false;
                        }
                    }
                    (None, None) => {}
                    _ => return false,
                }

                match (err_a, err_b) {
                    (Some(a), Some(b)) => {
                        if !self.component_val_type(*a, *b) {
                            return false;
                        }
                    }
                    (None, None) => {}
                    _ => return false,
                }

                true
            }
            (ComponentDefinedType::Own(a), ComponentDefinedType::Own(b)) => self.type_id(*a, *b),
            (ComponentDefinedType::Borrow(a), ComponentDefinedType::Borrow(b)) => {
                self.type_id(*a, *b)
            }
            _ => false,
        }
    }
}

/// Represents a type cache key.
#[derive(Clone)]
pub struct TypeCacheKey {
    types: Rc<Types>,
    comparisons: Rc<RefCell<TypeComparisonMap>>,
    resources: Rc<RefCell<ResourceMap>>,
    name: Option<String>,
    ty: TypeId,
    hash: u64,
}

impl Hash for TypeCacheKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.hash.hash(state);
    }
}

impl fmt::Debug for TypeCacheKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TypeCacheKey")
            .field("types", &"...")
            .field("comparisons", &"...")
            .field("resources", &"...")
            .field("name", &self.name)
            .field("ty", &self.ty)
            .field("hash", &self.hash)
            .finish()
    }
}

impl PartialEq for TypeCacheKey {
    fn eq(&self, other: &Self) -> bool {
        if self.hash != other.hash || self.name != other.name {
            return false;
        }

        let mut comparisons = self.comparisons.borrow_mut();
        let resources = self.resources.borrow();
        let mut comparer = TypeComparer {
            types: self.types.as_ref(),
            comparisons: &mut comparisons,
            resources: &resources,
        };
        comparer.type_id(self.ty, other.ty)
    }
}

impl Eq for TypeCacheKey {}

/// Represents a cache of wasmparser types.
///
/// This is used to deduplicate types as a package is parsed.
pub struct TypeCache {
    /// The wasmparser types collection.
    types: Rc<Types>,
    /// A map of a wasmparser type id to its hash.
    hashes: TypeHashMap,
    /// A map of wasmparser type ids to the comparison result.
    comparisons: Rc<RefCell<TypeComparisonMap>>,
    /// A map of wasmparser resource ids to their mapped ids.
    resources: Rc<RefCell<ResourceMap>>,
    /// A map of type cache keys to the resolved extern type.
    cache: HashMap<TypeCacheKey, super::Type>,
}

impl TypeCache {
    /// Creates a new type cache with the given wasmparser types collection.
    pub fn new(types: Rc<Types>, resources: Rc<RefCell<ResourceMap>>) -> Self {
        Self {
            types,
            hashes: Default::default(),
            comparisons: Default::default(),
            resources,
            cache: Default::default(),
        }
    }

    /// Gets a key for the cache for the given type.
    pub fn key(&mut self, name: Option<&str>, ty: TypeId) -> TypeCacheKey {
        let hash = match self.hashes.get(&ty) {
            Some(hash) => *hash,
            None => {
                let mut state = DefaultHasher::new();
                name.hash(&mut state);

                let mut hasher = TypeHasher {
                    types: &self.types,
                    resources: &self.resources.borrow(),
                    state: &mut state,
                };

                hasher.type_id(ty);
                state.finish()
            }
        };

        TypeCacheKey {
            types: self.types.clone(),
            comparisons: self.comparisons.clone(),
            resources: self.resources.clone(),
            name: name.map(ToOwned::to_owned),
            ty,
            hash,
        }
    }

    /// Gets a type from the cache by key.
    pub fn get(&mut self, key: &TypeCacheKey) -> Option<super::Type> {
        self.cache.get(key).copied()
    }

    /// Inserts a new key into the cache.
    ///
    /// Panics if the key is already present.
    pub fn insert(&mut self, key: TypeCacheKey, ty: super::Type) {
        let prev = self.cache.insert(key, ty);
        assert!(prev.is_none());
    }
}
