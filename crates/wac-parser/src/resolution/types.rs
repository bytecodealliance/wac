use super::{serialize_arena, serialize_id, serialize_optional_id, FuncKind, ItemKind, ScopeId};
use anyhow::{bail, Context, Result};
use id_arena::{Arena, Id};
use indexmap::{IndexMap, IndexSet};
use serde::Serialize;
use std::{
    collections::{HashMap, HashSet},
    fmt,
};

/// An identifier for value types.
pub type DefinedTypeId = Id<DefinedType>;

/// An identifier for resource types.
pub type ResourceId = Id<Resource>;

/// An identifier for function types.
pub type FuncId = Id<Func>;

/// An identifier for interface types.
pub type InterfaceId = Id<Interface>;

/// An identifier for world types.
pub type WorldId = Id<World>;

/// An identifier for module types.
pub type ModuleId = Id<Module>;

/// Represents a collection of type definitions.
#[derive(Default, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Definitions {
    /// The defined value types.
    #[serde(serialize_with = "serialize_arena")]
    pub types: Arena<DefinedType>,
    /// The defined resources.
    #[serde(serialize_with = "serialize_arena")]
    pub resources: Arena<Resource>,
    /// The defined function types.
    #[serde(serialize_with = "serialize_arena")]
    pub funcs: Arena<Func>,
    /// The defined interfaces (i.e. instance types).
    #[serde(serialize_with = "serialize_arena")]
    pub interfaces: Arena<Interface>,
    /// The defined worlds (i.e. component types).
    #[serde(serialize_with = "serialize_arena")]
    pub worlds: Arena<World>,
    /// The defined module types.
    #[serde(serialize_with = "serialize_arena")]
    pub modules: Arena<Module>,
}

/// Represent a component model type.
#[derive(Debug, Clone, Copy, Serialize, Hash, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub enum Type {
    /// The type is a function type.
    Func(#[serde(serialize_with = "serialize_id")] FuncId),
    /// The type is a defined value type.
    Value(#[serde(serialize_with = "serialize_id")] DefinedTypeId),
    /// The type is an interface (i.e. instance type).
    Interface(#[serde(serialize_with = "serialize_id")] InterfaceId),
    /// The type is a world (i.e. component type).
    World(#[serde(serialize_with = "serialize_id")] WorldId),
    /// The type is a core module type.
    Module(#[serde(serialize_with = "serialize_id")] ModuleId),
}

impl Type {
    pub(crate) fn display<'a>(&'a self, definitions: &'a Definitions) -> impl fmt::Display + 'a {
        TypeDisplay {
            ty: self,
            definitions,
        }
    }
}

struct TypeDisplay<'a> {
    ty: &'a Type,
    definitions: &'a Definitions,
}

impl fmt::Display for TypeDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.ty {
            Type::Func(_) => write!(f, "function type"),
            Type::Value(ty) => self.definitions.types[*ty].display(self.definitions).fmt(f),
            Type::Interface(_) => write!(f, "interface"),
            Type::World(_) => write!(f, "world"),
            Type::Module(_) => write!(f, "module type"),
        }
    }
}

/// Represents a primitive type.
#[derive(Debug, Copy, Clone, Eq, Hash, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum PrimitiveType {
    /// A `u8` type.
    U8,
    /// A `s8` type.
    S8,
    /// A `u16` type.
    U16,
    /// A `s16` type.
    S16,
    /// A `u32` type.
    U32,
    /// A `s32` type.
    S32,
    /// A `u64` type.
    U64,
    /// A `s64` type.
    S64,
    /// A `float32` type.
    Float32,
    /// A `float64` type.
    Float64,
    /// A `char` type.
    Char,
    /// A `bool` type.
    Bool,
    /// A `string` type.
    String,
}

impl fmt::Display for PrimitiveType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::U8 => write!(f, "u8"),
            Self::S8 => write!(f, "s8"),
            Self::U16 => write!(f, "u16"),
            Self::S16 => write!(f, "s16"),
            Self::U32 => write!(f, "u32"),
            Self::S32 => write!(f, "s32"),
            Self::U64 => write!(f, "u64"),
            Self::S64 => write!(f, "s64"),
            Self::Float32 => write!(f, "float32"),
            Self::Float64 => write!(f, "float64"),
            Self::Char => write!(f, "char"),
            Self::Bool => write!(f, "bool"),
            Self::String => write!(f, "string"),
        }
    }
}

impl From<wasmparser::PrimitiveValType> for PrimitiveType {
    fn from(value: wasmparser::PrimitiveValType) -> Self {
        match value {
            wasmparser::PrimitiveValType::Bool => Self::Bool,
            wasmparser::PrimitiveValType::S8 => Self::S8,
            wasmparser::PrimitiveValType::U8 => Self::U8,
            wasmparser::PrimitiveValType::S16 => Self::S16,
            wasmparser::PrimitiveValType::U16 => Self::U16,
            wasmparser::PrimitiveValType::S32 => Self::S32,
            wasmparser::PrimitiveValType::U32 => Self::U32,
            wasmparser::PrimitiveValType::S64 => Self::S64,
            wasmparser::PrimitiveValType::U64 => Self::U64,
            wasmparser::PrimitiveValType::Float32 => Self::Float32,
            wasmparser::PrimitiveValType::Float64 => Self::Float64,
            wasmparser::PrimitiveValType::Char => Self::Char,
            wasmparser::PrimitiveValType::String => Self::String,
        }
    }
}

/// Represents a value type.
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub enum ValueType {
    /// A primitive value type.
    Primitive(PrimitiveType),
    /// A defined value type.
    Defined(DefinedTypeId),
}

impl Serialize for ValueType {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Primitive(ty) => ty.serialize(serializer),
            Self::Defined(ty) => serialize_id(ty, serializer),
        }
    }
}

/// Represents a defined value type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum DefinedType {
    /// A primitive type.
    Primitive(PrimitiveType),
    /// A tuple type.
    Tuple(Vec<ValueType>),
    /// A list type.
    List(ValueType),
    /// An option type.
    Option(ValueType),
    /// A result type.
    Result {
        /// The result's `ok` type.
        ok: Option<ValueType>,
        /// The result's `err` type.
        err: Option<ValueType>,
    },
    /// The type is a borrow of a resource type.
    Borrow(#[serde(serialize_with = "serialize_id")] ResourceId),
    /// The type is a resource type.
    Resource(#[serde(serialize_with = "serialize_id")] ResourceId),
    /// The type is a variant type.
    Variant(Variant),
    /// The type is a record type.
    Record(Record),
    /// The type is a flags type.
    Flags(Flags),
    /// The type is an enum.
    Enum(Enum),
    /// The type is an alias to another type.
    Alias(ValueType),
}

impl DefinedType {
    pub(crate) fn display<'a>(&'a self, definitions: &'a Definitions) -> impl fmt::Display + 'a {
        DefinedTypeDisplay {
            ty: self,
            definitions,
        }
    }
}

struct DefinedTypeDisplay<'a> {
    ty: &'a DefinedType,
    definitions: &'a Definitions,
}

impl fmt::Display for DefinedTypeDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.ty {
            DefinedType::Primitive(ty) => write!(f, "{ty}"),
            DefinedType::Tuple(_) => write!(f, "tuple"),
            DefinedType::List(_) => write!(f, "list"),
            DefinedType::Option(_) => write!(f, "option"),
            DefinedType::Result { .. } => write!(f, "result"),
            DefinedType::Borrow(_) => write!(f, "borrow"),
            DefinedType::Resource(_) => write!(f, "resource"),
            DefinedType::Variant(_) => write!(f, "variant"),
            DefinedType::Record(_) => write!(f, "record"),
            DefinedType::Flags(_) => write!(f, "flags"),
            DefinedType::Enum(_) => write!(f, "enum"),
            DefinedType::Alias(ValueType::Primitive(ty)) => write!(f, "{ty}"),
            DefinedType::Alias(ValueType::Defined(id)) => {
                self.definitions.types[*id].display(self.definitions).fmt(f)
            }
        }
    }
}

/// Represents a resource method.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ResourceMethod {
    /// The kind of resource method.
    pub kind: FuncKind,
    /// The method's type.
    #[serde(serialize_with = "serialize_id")]
    pub ty: FuncId,
}

/// Represents a resource type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Resource {
    /// The resource methods.
    ///
    /// The resource's constructor uses an empty name.
    #[serde(skip_serializing_if = "IndexMap::is_empty")]
    pub methods: IndexMap<String, ResourceMethod>,
}

/// Represents a variant.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Variant {
    /// The variant cases.
    pub cases: IndexMap<String, Option<ValueType>>,
}

/// Represents a record type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Record {
    /// The record fields.
    pub fields: IndexMap<String, ValueType>,
}

/// Represents a flags type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Flags(pub IndexSet<String>);

/// Represents an enum type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Enum(pub IndexSet<String>);

/// Represents a function type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Func {
    /// The parameters of the function.
    pub params: IndexMap<String, ValueType>,
    /// The results of the function.
    pub results: Option<FuncResult>,
}

/// Represents a function result.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum FuncResult {
    /// A scalar result.
    Scalar(ValueType),
    /// A list of named results.
    List(IndexMap<String, ValueType>),
}

/// Represents an external item (imported or exported) from an interface or world.
#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum Extern {
    /// The item is a type used from an interface.
    #[serde(rename_all = "camelCase")]
    Use {
        /// The interface the type was sourced from.
        #[serde(serialize_with = "serialize_id")]
        interface: InterfaceId,
        /// The export index on the interface for the type.
        export_index: usize,
        /// The value type.
        #[serde(serialize_with = "serialize_id")]
        ty: DefinedTypeId,
    },
    /// The item is another kind of extern.
    Kind(ItemKind),
}

impl Extern {
    /// Gets the extern kind of the item.
    pub fn kind(&self) -> ItemKind {
        match self {
            Self::Use { ty, .. } => ItemKind::Type(Type::Value(*ty)),
            Self::Kind(kind) => *kind,
        }
    }
}

/// Represents a map of extern items.
pub type ExternMap = IndexMap<String, Extern>;

/// Represents an interface (i.e. instance type).
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Interface {
    /// The identifier of the interface.
    ///
    /// This may be `None` for inline interfaces.
    pub id: Option<String>,
    /// The exported items of the interface.
    pub exports: ExternMap,
    /// The scope associated with a defined interface.
    ///
    /// This is `None` for foreign interfaces.
    #[serde(serialize_with = "serialize_optional_id")]
    pub scope: Option<ScopeId>,
}

/// Represents a world.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct World {
    /// The imported items of the world.
    pub imports: ExternMap,
    /// The exported items of the world.
    pub exports: ExternMap,
    /// The scope associated with a defined world.
    ///
    /// This is `None` for foreign worlds.
    #[serde(serialize_with = "serialize_optional_id")]
    pub scope: Option<ScopeId>,
}

/// Represents a core module type.
#[derive(Debug, Clone, Serialize)]
pub struct Module {
    /// The imports of the module type.
    pub imports: IndexMap<(String, String), CoreExtern>,
    /// The exports of the module type.
    pub exports: IndexMap<String, CoreExtern>,
}

/// Represents a core extern imported or exported from a core module.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum CoreExtern {
    /// The item is a function.
    Func(CoreFunc),
    /// The item is a table.
    #[serde(rename_all = "camelCase")]
    Table {
        /// The table's element type.
        element_type: CoreRefType,
        /// Initial size of this table, in elements.
        initial: u32,
        /// Optional maximum size of the table, in elements.
        maximum: Option<u32>,
    },
    /// The item is a memory.
    #[serde(rename_all = "camelCase")]
    Memory {
        /// Whether or not this is a 64-bit memory, using i64 as an index. If this
        /// is false it's a 32-bit memory using i32 as an index.
        ///
        /// This is part of the memory64 proposal in WebAssembly.
        memory64: bool,

        /// Whether or not this is a "shared" memory, indicating that it should be
        /// send-able across threads and the `maximum` field is always present for
        /// valid types.
        ///
        /// This is part of the threads proposal in WebAssembly.
        shared: bool,

        /// Initial size of this memory, in wasm pages.
        ///
        /// For 32-bit memories (when `memory64` is `false`) this is guaranteed to
        /// be at most `u32::MAX` for valid types.
        initial: u64,

        /// Optional maximum size of this memory, in wasm pages.
        ///
        /// For 32-bit memories (when `memory64` is `false`) this is guaranteed to
        /// be at most `u32::MAX` for valid types. This field is always present for
        /// valid wasm memories when `shared` is `true`.
        maximum: Option<u64>,
    },
    /// The item is a global.
    #[serde(rename_all = "camelCase")]
    Global {
        /// The global's type.
        content_type: CoreType,
        /// Whether or not the global is mutable.
        mutable: bool,
    },
    /// The item is a tag.
    Tag(CoreFunc),
}

impl fmt::Display for CoreExtern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Func(_) => write!(f, "function"),
            Self::Table { .. } => write!(f, "table"),
            Self::Memory { .. } => write!(f, "memory"),
            Self::Global { .. } => write!(f, "global"),
            Self::Tag(_) => write!(f, "tag"),
        }
    }
}

impl From<wasmparser::TableType> for CoreExtern {
    fn from(ty: wasmparser::TableType) -> Self {
        Self::Table {
            element_type: ty.element_type.into(),
            initial: ty.initial,
            maximum: ty.maximum,
        }
    }
}

impl From<wasmparser::MemoryType> for CoreExtern {
    fn from(ty: wasmparser::MemoryType) -> Self {
        Self::Memory {
            memory64: ty.memory64,
            shared: ty.shared,
            initial: ty.initial,
            maximum: ty.maximum,
        }
    }
}

impl From<wasmparser::GlobalType> for CoreExtern {
    fn from(ty: wasmparser::GlobalType) -> Self {
        Self::Global {
            content_type: ty.content_type.into(),
            mutable: ty.mutable,
        }
    }
}

/// Represents the value types in a WebAssembly module.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum CoreType {
    /// The value type is i32.
    I32,
    /// The value type is i64.
    I64,
    /// The value type is f32.
    F32,
    /// The value type is f64.
    F64,
    /// The value type is v128.
    V128,
    /// The value type is a reference.
    Ref(CoreRefType),
}

impl fmt::Display for CoreType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::I32 => write!(f, "i32"),
            Self::I64 => write!(f, "i64"),
            Self::F32 => write!(f, "f32"),
            Self::F64 => write!(f, "f64"),
            Self::V128 => write!(f, "v128"),
            Self::Ref(r) => r.fmt(f),
        }
    }
}

impl From<wasmparser::ValType> for CoreType {
    fn from(ty: wasmparser::ValType) -> Self {
        match ty {
            wasmparser::ValType::I32 => Self::I32,
            wasmparser::ValType::I64 => Self::I64,
            wasmparser::ValType::F32 => Self::F32,
            wasmparser::ValType::F64 => Self::F64,
            wasmparser::ValType::V128 => Self::V128,
            wasmparser::ValType::Ref(ty) => Self::Ref(ty.into()),
        }
    }
}

/// Represents the type of a reference in a WebAssembly module.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CoreRefType {
    /// Whether or not the ref type is nullable.
    pub nullable: bool,
    /// The heap type of the ref type.
    pub heap_type: HeapType,
}

impl fmt::Display for CoreRefType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match (self.nullable, self.heap_type) {
            (true, HeapType::Func) => "funcref",
            (true, HeapType::Extern) => "externref",
            (true, HeapType::Indexed(i)) => return write!(f, "(ref null {i})"),
            (true, HeapType::Any) => "anyref",
            (true, HeapType::None) => "nullref",
            (true, HeapType::NoExtern) => "nullexternref",
            (true, HeapType::NoFunc) => "nullfuncref",
            (true, HeapType::Eq) => "eqref",
            (true, HeapType::Struct) => "structref",
            (true, HeapType::Array) => "arrayref",
            (true, HeapType::I31) => "i31ref",
            (false, HeapType::Func) => "(ref func)",
            (false, HeapType::Extern) => "(ref extern)",
            (false, HeapType::Indexed(i)) => return write!(f, "(ref {i})"),
            (false, HeapType::Any) => "(ref any)",
            (false, HeapType::None) => "(ref none)",
            (false, HeapType::NoExtern) => "(ref noextern)",
            (false, HeapType::NoFunc) => "(ref nofunc)",
            (false, HeapType::Eq) => "(ref eq)",
            (false, HeapType::Struct) => "(ref struct)",
            (false, HeapType::Array) => "(ref array)",
            (false, HeapType::I31) => "(ref i31)",
        };

        f.write_str(s)
    }
}

impl From<wasmparser::RefType> for CoreRefType {
    fn from(ty: wasmparser::RefType) -> Self {
        Self {
            nullable: ty.is_nullable(),
            heap_type: ty.heap_type().into(),
        }
    }
}

/// A heap type of a reference type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum HeapType {
    /// User defined type at the given index.
    Indexed(u32),
    /// Untyped (any) function.
    Func,
    /// External heap type.
    Extern,
    /// The `any` heap type.
    Any,
    /// The `none` heap type.
    None,
    /// The `noextern` heap type.
    NoExtern,
    /// The `nofunc` heap type.
    NoFunc,
    /// The `eq` heap type.
    Eq,
    /// The `struct` heap type. The common supertype of all struct types.
    Struct,
    /// The `array` heap type. The common supertype of all array types.
    Array,
    /// The i31 heap type.
    I31,
}

impl From<wasmparser::HeapType> for HeapType {
    fn from(ty: wasmparser::HeapType) -> Self {
        match ty {
            wasmparser::HeapType::Any => Self::Any,
            wasmparser::HeapType::Func => Self::Func,
            wasmparser::HeapType::Extern => Self::Extern,
            wasmparser::HeapType::Eq => Self::Eq,
            wasmparser::HeapType::I31 => Self::I31,
            wasmparser::HeapType::None => Self::None,
            wasmparser::HeapType::NoExtern => Self::NoExtern,
            wasmparser::HeapType::NoFunc => Self::NoFunc,
            wasmparser::HeapType::Struct => Self::Struct,
            wasmparser::HeapType::Array => Self::Array,
            wasmparser::HeapType::Indexed(index) => Self::Indexed(index),
        }
    }
}

/// Represents a core function type in a WebAssembly module.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CoreFunc {
    /// The parameters of the function.
    pub params: Vec<CoreType>,
    /// The results of the function.
    pub results: Vec<CoreType>,
}

impl fmt::Display for CoreFunc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;

        for (i, ty) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            write!(f, "{}", ty)?;
        }

        write!(f, "] -> [")?;

        for (i, ty) in self.results.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            write!(f, "{}", ty)?;
        }

        write!(f, "]")
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum CheckKind {
    Covariant,
    Contravariant,
}

struct ResourceMap {
    kind: CheckKind,
    map: HashMap<ResourceId, ResourceId>,
}

impl ResourceMap {
    fn new(kind: CheckKind) -> Self {
        Self {
            kind,
            map: Default::default(),
        }
    }

    fn insert(&mut self, a: ResourceId, b: ResourceId) {
        self.map.insert(a, b);
    }

    fn is_subtype(&self, checker: &SubtypeChecker, a: ResourceId, b: ResourceId) -> Result<()> {
        if self.map.get(&a) != Some(&b) && self.map.get(&b) != Some(&a) {
            bail!("mismatched resource types");
        }

        let a = &checker.definitions.resources[a];
        let b = &checker.definitions.resources[b];

        for (k, a) in a.methods.iter() {
            match b.methods.get(k) {
                Some(b) => {
                    match self.kind {
                        CheckKind::Covariant => checker.func(a.ty, b.ty),
                        CheckKind::Contravariant => checker.func(b.ty, a.ty),
                    }
                    .with_context(|| {
                        if k.is_empty() {
                            "mismatched type for constructor".to_string()
                        } else {
                            format!("mismatched type for method `{k}`")
                        }
                    })?;
                }
                None => {
                    if k.is_empty() {
                        bail!("missing expected constructor");
                    } else {
                        bail!("missing expected method `{k}`");
                    }
                }
            }
        }

        Ok(())
    }
}

/// Implements a subtype checker.
///
/// Subtype checking is used to type check instantiation arguments.
pub struct SubtypeChecker<'a> {
    definitions: &'a Definitions,
    cache: HashSet<(ItemKind, ItemKind)>,
    resource_map: Vec<ResourceMap>,
}

impl<'a> SubtypeChecker<'a> {
    /// Creates a new subtype checker.
    pub fn new(definitions: &'a Definitions) -> Self {
        Self {
            definitions,
            cache: Default::default(),
            resource_map: Default::default(),
        }
    }

    /// Checks if `a` is a subtype of `b`.
    pub fn is_subtype(&mut self, a: ItemKind, b: ItemKind) -> Result<()> {
        if self.cache.contains(&(a, b)) {
            return Ok(());
        }

        let mut check = || match (a, b) {
            (ItemKind::Type(a), ItemKind::Type(b)) => self.ty(a, b),
            (ItemKind::Func(a), ItemKind::Func(b)) => self.func(a, b),
            (ItemKind::Instance(a), ItemKind::Instance(b)) => self.interface(a, b),
            (ItemKind::Instantiation(a), ItemKind::Instantiation(b)) => {
                let a = &self.definitions.worlds[a];
                let b = &self.definitions.worlds[b];
                self.interface_exports(&a.exports, &b.exports)
            }
            (ItemKind::Instantiation(a), ItemKind::Instance(b)) => {
                let a = &self.definitions.worlds[a];
                let b = &self.definitions.interfaces[b];
                self.interface_exports(&a.exports, &b.exports)
            }
            (ItemKind::Instance(a), ItemKind::Instantiation(b)) => {
                let a = &self.definitions.interfaces[a];
                let b = &self.definitions.worlds[b];
                self.interface_exports(&a.exports, &b.exports)
            }
            (ItemKind::Component(a), ItemKind::Component(b)) => self.world(a, b),
            (ItemKind::Module(a), ItemKind::Module(b)) => self.module(a, b),
            (ItemKind::Value(a), ItemKind::Value(b)) => self.value_type(a, b),
            _ => bail!(
                "expected {a}, found {b}",
                a = a.display(self.definitions),
                b = b.display(self.definitions)
            ),
        };

        let result = check();
        if result.is_ok() {
            self.cache.insert((a, b));
        }

        result
    }

    fn ty(&mut self, a: Type, b: Type) -> Result<()> {
        match (a, b) {
            (Type::Func(a), Type::Func(b)) => return self.func(a, b),
            (Type::Value(a), Type::Value(b)) => return self.defined_type(a, b),
            (Type::Interface(a), Type::Interface(b)) => return self.interface(a, b),
            (Type::World(a), Type::World(b)) => return self.world(a, b),
            (Type::Module(a), Type::Module(b)) => return self.module(a, b),
            _ => {}
        }

        bail!(
            "expected {a}, found {b}",
            a = a.display(self.definitions),
            b = b.display(self.definitions)
        )
    }

    fn func(&self, a: FuncId, b: FuncId) -> Result<()> {
        if a == b {
            return Ok(());
        }

        let a = &self.definitions.funcs[a];
        let b = &self.definitions.funcs[b];

        // Note: currently subtyping for functions is done in terms of equality
        // rather than actual subtyping; the reason for this is that implementing
        // runtimes don't yet support more complex subtyping rules.

        if a.params.len() != b.params.len() {
            bail!(
                "expected function with parameter count {}, found parameter count {}",
                a.params.len(),
                b.params.len(),
            );
        }

        for (i, ((an, a), (bn, b))) in a.params.iter().zip(b.params.iter()).enumerate() {
            if an != bn {
                bail!("expected function parameter {i} to be named `{an}`, found name `{bn}`");
            }

            self.value_type(*a, *b)
                .with_context(|| format!("mismatched type for function parameter `{an}`"))?;
        }

        match (&a.results, &b.results) {
            (None, None) => {}
            (None, Some(_)) => {
                bail!("expected function without results, found function with results")
            }
            (Some(_), None) => {
                bail!("expected function with results, found function without results")
            }
            (Some(FuncResult::Scalar(a)), Some(FuncResult::Scalar(b))) => {
                self.value_type(*a, *b)
                    .context("mismatched type for function result")?;
            }
            (Some(FuncResult::Scalar(_)), Some(_)) => {
                bail!("expected function with scalar result, found function with named results")
            }
            (Some(FuncResult::List(a)), Some(FuncResult::List(b))) => {
                for (i, ((an, a), (bn, b))) in a.iter().zip(b.iter()).enumerate() {
                    if an != bn {
                        bail!("expected function result {i} to be named `{an}`, found name `{bn}`");
                    }

                    self.value_type(*a, *b)
                        .with_context(|| format!("mismatched type for function result `{an}`"))?;
                }
            }
            (Some(FuncResult::List(_)), Some(_)) => {
                bail!("expected function with named results, found function with scalar result")
            }
        }

        Ok(())
    }

    fn interface_exports(&mut self, a: &ExternMap, b: &ExternMap) -> Result<()> {
        // Before we do anything, we need to populate a resource mapping
        let mut map = ResourceMap::new(CheckKind::Covariant);
        for (k, a) in a.iter() {
            match b.get(k) {
                Some(b) => match (a.kind(), b.kind()) {
                    (ItemKind::Type(Type::Value(a)), ItemKind::Type(Type::Value(b))) => {
                        let a = &self.definitions.types[a];
                        let b = &self.definitions.types[b];
                        match (a, b) {
                            (DefinedType::Resource(a), DefinedType::Resource(b)) => {
                                map.insert(*a, *b);
                            }
                            _ => continue,
                        }
                    }
                    _ => continue,
                },
                None => continue,
            }
        }

        self.resource_map.push(map);

        let mut check = || {
            // For instance type subtyping, all exports in the other
            // instance type must be present in this instance type's
            // exports (i.e. it can export *more* than what this instance
            // type needs).
            for (k, a) in a.iter() {
                match b.get(k) {
                    Some(b) => {
                        self.is_subtype(a.kind(), b.kind())
                            .with_context(|| format!("mismatched type for export `{k}`"))?;
                    }
                    None => bail!("missing expected export `{k}`"),
                }
            }

            Ok(())
        };

        let result = check();
        self.resource_map.pop();
        result
    }

    fn interface(&mut self, a: InterfaceId, b: InterfaceId) -> Result<()> {
        if a == b {
            return Ok(());
        }

        let a = &self.definitions.interfaces[a];
        let b = &self.definitions.interfaces[b];
        self.interface_exports(&a.exports, &b.exports)
    }

    fn world(&mut self, a: WorldId, b: WorldId) -> Result<()> {
        if a == b {
            return Ok(());
        }

        let a = &self.definitions.worlds[a];
        let b = &self.definitions.worlds[b];

        // Before we do anything, we need to populate a resource mapping
        let mut map = ResourceMap::new(CheckKind::Contravariant);
        for (k, a) in a.imports.iter() {
            match b.imports.get(k) {
                Some(b) => match (a.kind(), b.kind()) {
                    (ItemKind::Type(Type::Value(a)), ItemKind::Type(Type::Value(b))) => {
                        let a = &self.definitions.types[a];
                        let b = &self.definitions.types[b];
                        match (a, b) {
                            (DefinedType::Resource(a), DefinedType::Resource(b)) => {
                                map.insert(*a, *b);
                            }
                            _ => continue,
                        }
                    }
                    _ => continue,
                },
                None => continue,
            }
        }

        self.resource_map.push(map);

        let mut check = || {
            // For component type subtyping, all exports in the other component
            // type must be present in this component type's exports (i.e. it
            // can export *more* than what this component type needs).
            // However, for imports, the check is reversed (i.e. it is okay
            // to import *less* than what this component type needs).
            for (k, a) in a.imports.iter() {
                match b.imports.get(k) {
                    Some(b) => {
                        self.is_subtype(b.kind(), a.kind())
                            .with_context(|| format!("mismatched type for import `{k}`"))?;
                    }
                    None => bail!("missing expected import `{k}`"),
                }
            }

            for (k, b) in b.exports.iter() {
                match a.exports.get(k) {
                    Some(a) => {
                        self.is_subtype(a.kind(), b.kind())
                            .with_context(|| format!("mismatched type for export `{k}"))?;
                    }
                    None => bail!("missing expected export `{k}`"),
                }
            }

            Ok(())
        };

        let result = check();
        self.resource_map.pop();
        result
    }

    fn module(&mut self, a: ModuleId, b: ModuleId) -> Result<()> {
        if a == b {
            return Ok(());
        }

        let a = &self.definitions.modules[a];
        let b = &self.definitions.modules[b];

        // For module type subtyping, all exports in the other module
        // type must be present in expected module type's exports (i.e. it
        // can export *more* than what is expected module type needs).
        // However, for imports, the check is reversed (i.e. it is okay
        // to import *less* than what this module type needs).
        for (k, a) in a.imports.iter() {
            match b.imports.get(k) {
                Some(b) => {
                    Self::core_extern(b, a).with_context(|| {
                        format!("mismatched type for import `{m}::{n}`", m = k.0, n = k.1)
                    })?;
                }
                None => bail!("missing expected import `{m}::{n}`", m = k.0, n = k.1),
            }
        }

        for (k, b) in b.exports.iter() {
            match a.exports.get(k) {
                Some(a) => {
                    Self::core_extern(a, b)
                        .with_context(|| format!("mismatched type for export `{k}"))?;
                }
                None => bail!("missing expected export `{k}`"),
            }
        }

        Ok(())
    }

    fn core_extern(a: &CoreExtern, b: &CoreExtern) -> Result<()> {
        macro_rules! limits_match {
            ($ai:expr, $am:expr, $bi:expr, $bm:expr) => {{
                $ai >= $bi
                    && match ($am, $bm) {
                        (Some(am), Some(bm)) => am <= bm,
                        (None, Some(_)) => false,
                        _ => true,
                    }
            }};
        }

        match (a, b) {
            (CoreExtern::Func(a), CoreExtern::Func(b)) => return Self::core_func(a, b),
            (
                CoreExtern::Table {
                    element_type: ae,
                    initial: ai,
                    maximum: am,
                },
                CoreExtern::Table {
                    element_type: be,
                    initial: bi,
                    maximum: bm,
                },
            ) => {
                if ae != be {
                    bail!("expected table element type {ae}, found {be}");
                }

                if !limits_match!(ai, am, bi, bm) {
                    bail!("mismatched table limits");
                }

                return Ok(());
            }
            (
                CoreExtern::Memory {
                    memory64: a64,
                    shared: ashared,
                    initial: ai,
                    maximum: am,
                },
                CoreExtern::Memory {
                    memory64: b64,
                    shared: bshared,
                    initial: bi,
                    maximum: bm,
                },
            ) => {
                if ashared != bshared {
                    bail!("mismatched shared flag for memories");
                }

                if a64 != b64 {
                    bail!("mismatched memory64 flag for memories");
                }

                if !limits_match!(ai, am, bi, bm) {
                    bail!("mismatched memory limits");
                }

                return Ok(());
            }
            (
                CoreExtern::Global {
                    content_type: at,
                    mutable: am,
                },
                CoreExtern::Global {
                    content_type: bt,
                    mutable: bm,
                },
            ) => {
                if am != bm {
                    bail!("mismatched mutable flag for globals");
                }

                if at != bt {
                    bail!("expected global type {at}, found {bt}");
                }

                return Ok(());
            }
            (CoreExtern::Tag(a), CoreExtern::Tag(b)) => return Self::core_func(a, b),
            _ => {}
        }

        bail!("expected {a}, found {b}")
    }

    fn core_func(a: &CoreFunc, b: &CoreFunc) -> Result<()> {
        if a != b {
            bail!("expected {a}, found {b}");
        }

        Ok(())
    }

    fn resolve_alias(&self, mut id: DefinedTypeId) -> DefinedTypeId {
        loop {
            let ty = &self.definitions.types[id];
            if let DefinedType::Alias(ValueType::Defined(next)) = ty {
                id = *next;
            } else {
                return id;
            }
        }
    }

    fn value_type(&self, a: ValueType, b: ValueType) -> Result<()> {
        match (a, b) {
            (ValueType::Primitive(a), ValueType::Primitive(b)) => Self::primitive(a, b),
            (ValueType::Primitive(a), ValueType::Defined(b)) => {
                let b = &self.definitions.types[self.resolve_alias(b)];
                if let DefinedType::Primitive(b) = b {
                    Self::primitive(a, *b)
                } else {
                    bail!("expected {a}, found {b}", b = b.display(self.definitions));
                }
            }
            (ValueType::Defined(a), ValueType::Primitive(b)) => {
                let a = &self.definitions.types[self.resolve_alias(a)];
                if let DefinedType::Primitive(a) = a {
                    Self::primitive(*a, b)
                } else {
                    bail!("expected {a}, found {b}", a = a.display(self.definitions));
                }
            }
            (ValueType::Defined(a), ValueType::Defined(b)) => self.defined_type(a, b),
        }
    }

    fn defined_type(
        &self,
        a: DefinedTypeId,
        b: DefinedTypeId,
    ) -> std::result::Result<(), anyhow::Error> {
        if a == b {
            return Ok(());
        }

        let a = &self.definitions.types[self.resolve_alias(a)];
        let b = &self.definitions.types[self.resolve_alias(b)];
        match (a, b) {
            (DefinedType::Primitive(a), DefinedType::Primitive(b)) => Self::primitive(*a, *b),
            (DefinedType::Tuple(a), DefinedType::Tuple(b)) => self.tuple(a, b),
            (DefinedType::List(a), DefinedType::List(b)) => self
                .value_type(*a, *b)
                .context("mismatched type for list element"),
            (DefinedType::Option(a), DefinedType::Option(b)) => self
                .value_type(*a, *b)
                .context("mismatched type for option"),
            (
                DefinedType::Result {
                    ok: a_ok,
                    err: a_err,
                },
                DefinedType::Result {
                    ok: b_ok,
                    err: b_err,
                },
            ) => {
                self.result("ok", a_ok, b_ok)?;
                self.result("err", a_err, b_err)
            }
            (DefinedType::Borrow(a), DefinedType::Borrow(b))
            | (DefinedType::Resource(a), DefinedType::Resource(b)) => {
                if a == b {
                    return Ok(());
                }

                if let Some(map) = self.resource_map.last() {
                    return map.is_subtype(self, *a, *b);
                }

                bail!("mismatched resource types")
            }
            (DefinedType::Variant(a), DefinedType::Variant(b)) => self.variant(a, b),
            (DefinedType::Record(a), DefinedType::Record(b)) => self.record(a, b),
            (DefinedType::Flags(a), DefinedType::Flags(b)) => Self::flags(a, b),
            (DefinedType::Enum(a), DefinedType::Enum(b)) => Self::enum_type(a, b),
            (DefinedType::Alias(_), _) => unreachable!("alias should have been resolved"),
            _ => {
                bail!(
                    "expected {a}, found {b}",
                    a = a.display(self.definitions),
                    b = b.display(self.definitions)
                )
            }
        }
    }

    fn result(&self, desc: &str, a: &Option<ValueType>, b: &Option<ValueType>) -> Result<()> {
        match (a, b) {
            (None, None) => Ok(()),
            (None, Some(_)) => bail!("expected no `{desc}` for result type"),
            (Some(_), None) => bail!("expected an `{desc}` for result type"),
            (Some(a), Some(b)) => self
                .value_type(*a, *b)
                .with_context(|| format!("mismatched type for result `{desc}`")),
        }
    }

    fn enum_type(a: &Enum, b: &Enum) -> Result<()> {
        if a.0.len() != b.0.len() {
            bail!(
                "expected an enum type case count of {a}, found a count of {b}",
                a = a.0.len(),
                b = b.0.len()
            );
        }

        if let Some((index, (a, b))) =
            a.0.iter()
                .zip(b.0.iter())
                .enumerate()
                .find(|(_, (a, b))| a != b)
        {
            bail!("expected enum case {index} to be named `{a}`, found an enum case named `{b}`");
        }

        Ok(())
    }

    fn flags(a: &Flags, b: &Flags) -> Result<()> {
        if a.0.len() != b.0.len() {
            bail!(
                "expected a flags type flag count of {a}, found a count of {b}",
                a = a.0.len(),
                b = b.0.len()
            );
        }

        if let Some((index, (a, b))) =
            a.0.iter()
                .zip(b.0.iter())
                .enumerate()
                .find(|(_, (a, b))| a != b)
        {
            bail!("expected flag {index} to be named `{a}`, found a flag named `{b}`");
        }

        Ok(())
    }

    fn record(&self, a: &Record, b: &Record) -> Result<()> {
        if a.fields.len() != b.fields.len() {
            bail!(
                "expected a record field count of {a}, found a count of {b}",
                a = a.fields.len(),
                b = b.fields.len()
            );
        }

        for (i, ((an, a), (bn, b))) in a.fields.iter().zip(b.fields.iter()).enumerate() {
            if an != bn {
                bail!("expected record field {i} to be named `{an}`, found a field named `{bn}`");
            }

            self.value_type(*a, *b)
                .with_context(|| format!("mismatched type for record field `{an}`"))?;
        }

        Ok(())
    }

    fn variant(&self, a: &Variant, b: &Variant) -> Result<()> {
        if a.cases.len() != b.cases.len() {
            bail!(
                "expected a variant case count of {a}, found a count of {b}",
                a = a.cases.len(),
                b = b.cases.len()
            );
        }

        for (i, ((an, a), (bn, b))) in a.cases.iter().zip(b.cases.iter()).enumerate() {
            if an != bn {
                bail!("expected variant case {i} to be named `{an}`, found a case named `{bn}`");
            }

            match (a, b) {
                (None, None) => {}
                (None, Some(_)) => {
                    bail!("expected variant case `{an}` to be untyped, found a typed case")
                }
                (Some(_), None) => {
                    bail!("expected variant case `{an}` to be typed, found an untyped case")
                }
                (Some(a), Some(b)) => self
                    .value_type(*a, *b)
                    .with_context(|| format!("mismatched type for variant case `{an}`"))?,
            }
        }

        Ok(())
    }

    fn tuple(&self, a: &Vec<ValueType>, b: &Vec<ValueType>) -> Result<()> {
        if a.len() != b.len() {
            bail!(
                "expected a tuple of size {a}, found a tuple of size {b}",
                a = a.len(),
                b = b.len()
            );
        }

        for (i, (a, b)) in a.iter().zip(b.iter()).enumerate() {
            self.value_type(*a, *b)
                .with_context(|| format!("mismatched type for tuple item {i}"))?;
        }

        Ok(())
    }

    fn primitive(a: PrimitiveType, b: PrimitiveType) -> Result<()> {
        // Note: currently subtyping for primitive types is done in terms of equality
        // rather than actual subtyping; the reason for this is that implementing
        // runtimes don't yet support more complex subtyping rules.
        if a != b {
            bail!("expected {a}, found {b}");
        }

        Ok(())
    }
}
