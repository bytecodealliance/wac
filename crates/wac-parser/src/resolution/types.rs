use super::{package::Package, serialize_arena, serialize_id, serialize_optional_id, ItemKind};
use anyhow::{bail, Context, Result};
use id_arena::{Arena, Id};
use indexmap::{IndexMap, IndexSet};
use serde::Serialize;
use std::{collections::HashSet, fmt};

/// An identifier for defined value types.
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

impl Definitions {
    /// Resolves a value type to a un-aliased value type.
    pub fn resolve_type(&self, mut ty: ValueType) -> ValueType {
        loop {
            match ty {
                ValueType::Defined { id, .. } => match &self.types[id] {
                    DefinedType::Alias(aliased) => ty = *aliased,
                    _ => return ty,
                },
                _ => return ty,
            }
        }
    }

    /// Resolves any aliased resource id to the underlying defined resource id.
    pub fn resolve_resource_id(&self, mut id: ResourceId) -> ResourceId {
        while let Some(alias_of) = &self.resources[id].alias_of {
            id = *alias_of;
        }

        id
    }

    /// Resolves any aliased resource id to the underlying defined resource.
    pub fn resolve_resource(&self, id: ResourceId) -> &Resource {
        let resolved = self.resolve_resource_id(id);
        &self.resources[resolved]
    }

    /// Resolves any aliased resource to the mutable underlying defined resource.
    pub fn resolve_resource_mut(&mut self, id: ResourceId) -> &mut Resource {
        let resolved = self.resolve_resource_id(id);
        &mut self.resources[resolved]
    }
}

/// Represent a component model type.
#[derive(Debug, Clone, Copy, Serialize, Hash, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub enum Type {
    /// The type is a function type.
    Func(#[serde(serialize_with = "serialize_id")] FuncId),
    /// The type is a value type.
    Value(ValueType),
    /// The type is an interface (i.e. instance type).
    Interface(#[serde(serialize_with = "serialize_id")] InterfaceId),
    /// The type is a world (i.e. component type).
    World(#[serde(serialize_with = "serialize_id")] WorldId),
    /// The type is a core module type.
    Module(#[serde(serialize_with = "serialize_id")] ModuleId),
}

impl Type {
    pub(crate) fn as_str(&self, definitions: &Definitions) -> &'static str {
        match self {
            Type::Func(_) => "function type",
            Type::Value(ty) => ty.as_str(definitions),
            Type::Interface(_) => "interface",
            Type::World(_) => "world",
            Type::Module(_) => "module type",
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

impl PrimitiveType {
    fn as_str(&self) -> &'static str {
        match self {
            Self::U8 => "u8",
            Self::S8 => "s8",
            Self::U16 => "u16",
            Self::S16 => "s16",
            Self::U32 => "u32",
            Self::S32 => "s32",
            Self::U64 => "u64",
            Self::S64 => "s64",
            Self::Float32 => "float32",
            Self::Float64 => "float64",
            Self::Char => "char",
            Self::Bool => "bool",
            Self::String => "string",
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
    /// The type is a borrow of a resource type.
    Borrow(ResourceId),
    /// The type is an owned resource type.
    Own(ResourceId),
    /// A defined value type.
    Defined {
        /// The id of the defined value type.
        id: DefinedTypeId,
        /// Whether or not the defined value type recursively contains a borrow.
        contains_borrow: bool,
    },
}

impl ValueType {
    /// Checks if the type contains a borrow.
    ///
    /// Function results may not return a type containing a borrow.
    pub(crate) fn contains_borrow(&self) -> bool {
        match self {
            ValueType::Primitive(_) | ValueType::Own(_) => false,
            ValueType::Borrow(_) => true,
            ValueType::Defined {
                contains_borrow, ..
            } => *contains_borrow,
        }
    }

    fn as_str(&self, definitions: &Definitions) -> &'static str {
        match self {
            Self::Primitive(ty) => ty.as_str(),
            Self::Borrow(_) => "borrow",
            Self::Own(_) => "own",
            Self::Defined { id, .. } => definitions.types[*id].as_str(definitions),
        }
    }
}

impl Serialize for ValueType {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Primitive(ty) => ty.serialize(serializer),
            Self::Borrow(id) => format!("borrow<{id}>", id = id.index()).serialize(serializer),
            Self::Own(id) => format!("own<{id}>", id = id.index()).serialize(serializer),
            Self::Defined { id, .. } => serialize_id(id, serializer),
        }
    }
}

/// Represents a defined value type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum DefinedType {
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
    /// The type is a variant type.
    Variant(Variant),
    /// The type is a record type.
    Record(Record),
    /// The type is a flags type.
    Flags(Flags),
    /// The type is an enum.
    Enum(Enum),
    /// The type is an alias to another value type.
    Alias(ValueType),
}

impl DefinedType {
    fn as_str(&self, definitions: &Definitions) -> &'static str {
        match self {
            DefinedType::Tuple(_) => "tuple",
            DefinedType::List(_) => "list",
            DefinedType::Option(_) => "option",
            DefinedType::Result { .. } => "result",
            DefinedType::Variant(_) => "variant",
            DefinedType::Record(_) => "record",
            DefinedType::Flags(_) => "flags",
            DefinedType::Enum(_) => "enum",
            DefinedType::Alias(ty) => ty.as_str(definitions),
        }
    }
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

pub(crate) fn method_extern_name(resource: &str, name: &str, kind: FuncKind) -> String {
    match kind {
        FuncKind::Free => unreachable!("a resource method cannot be a free function"),
        FuncKind::Method => format!("[method]{resource}.{name}"),
        FuncKind::Static => format!("[static]{resource}.{name}"),
        FuncKind::Constructor => format!("[constructor]{resource}"),
    }
}

/// Represents a resource type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Resource {
    /// The name of the resource.
    pub name: String,

    /// The id of the resource that was aliased.
    #[serde(
        serialize_with = "serialize_optional_id",
        skip_serializing_if = "Option::is_none"
    )]
    pub alias_of: Option<ResourceId>,
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
#[derive(Debug, Clone, Serialize, Default)]
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

/// Represents a used type.
#[derive(Debug, Clone, Serialize)]
pub struct UsedType {
    /// The interface the type was used from.
    #[serde(serialize_with = "serialize_id")]
    pub interface: InterfaceId,
    /// The original export name.
    ///
    /// This is `None` when the type was not renamed with an `as` clause.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
}

/// Represents an interface (i.e. instance type).
#[derive(Debug, Clone, Serialize, Default)]
#[serde(rename_all = "camelCase")]
pub struct Interface {
    /// The identifier of the interface.
    ///
    /// This may be `None` for inline interfaces.
    pub id: Option<String>,
    /// Represents a remapping of types that may occur when an interface is merged.
    ///
    /// The map is from the type present in this interface to a set of types
    /// originating from the merged interfaces.
    ///
    /// Encoding uses this map to populate the encoded type index map for the
    /// original types.
    #[serde(skip)]
    pub remapped_types: IndexMap<Type, IndexSet<Type>>,
    /// A map of exported name to information about the used type.
    pub uses: IndexMap<String, UsedType>,
    /// The exported items of the interface.
    pub exports: IndexMap<String, ItemKind>,
}

/// Represents a world.
#[derive(Debug, Clone, Serialize, Default)]
#[serde(rename_all = "camelCase")]
pub struct World {
    /// The identifier of the world.
    ///
    /// This may be `None` for worlds representing component types.
    pub id: Option<String>,
    /// A map of imported name to information about the used type.
    pub uses: IndexMap<String, UsedType>,
    /// The imported items of the world.
    pub imports: IndexMap<String, ItemKind>,
    /// The exported items of the world.
    pub exports: IndexMap<String, ItemKind>,
}

/// Represents a core module type.
#[derive(Debug, Clone, Serialize, Default)]
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
        val_type: CoreType,
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
            val_type: ty.content_type.into(),
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

impl From<CoreType> for wasm_encoder::ValType {
    fn from(value: CoreType) -> Self {
        match value {
            CoreType::I32 => Self::I32,
            CoreType::I64 => Self::I64,
            CoreType::F32 => Self::F32,
            CoreType::F64 => Self::F64,
            CoreType::V128 => Self::V128,
            CoreType::Ref(r) => Self::Ref(r.into()),
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
            (true, HeapType::Concrete(i)) => return write!(f, "(ref null {i})"),
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
            (false, HeapType::Concrete(i)) => return write!(f, "(ref {i})"),
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

impl From<CoreRefType> for wasm_encoder::RefType {
    fn from(value: CoreRefType) -> Self {
        wasm_encoder::RefType {
            nullable: value.nullable,
            heap_type: value.heap_type.into(),
        }
    }
}

/// A heap type of a reference type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Serialize)]
pub enum HeapType {
    /// User defined type at the given index.
    Concrete(u32),
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
            wasmparser::HeapType::Concrete(index) => {
                Self::Concrete(index.as_module_index().unwrap())
            }
        }
    }
}

impl From<HeapType> for wasm_encoder::HeapType {
    fn from(value: HeapType) -> Self {
        match value {
            HeapType::Concrete(index) => Self::Concrete(index),
            HeapType::Func => Self::Func,
            HeapType::Extern => Self::Extern,
            HeapType::Any => Self::Any,
            HeapType::None => Self::None,
            HeapType::NoExtern => Self::NoExtern,
            HeapType::NoFunc => Self::NoFunc,
            HeapType::Eq => Self::Eq,
            HeapType::Struct => Self::Struct,
            HeapType::Array => Self::Array,
            HeapType::I31 => Self::I31,
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

/// Represents the kind of subtyping check to perform.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum SubtypeCheckKind {
    /// The type is a covariant check.
    Covariant,
    /// The type is a contravariant check.
    Contravariant,
}

/// Implements a subtype checker.
///
/// Subtype checking is used to type check instantiation arguments.
pub struct SubtypeChecker<'a> {
    kinds: Vec<SubtypeCheckKind>,
    definitions: &'a Definitions,
    packages: &'a Arena<Package>,
    cache: HashSet<(ItemKind, ItemKind)>,
}

impl<'a> SubtypeChecker<'a> {
    /// Creates a new subtype checker.
    pub fn new(definitions: &'a Definitions, packages: &'a Arena<Package>) -> Self {
        Self {
            kinds: Default::default(),
            definitions,
            packages,
            cache: Default::default(),
        }
    }

    /// Checks if `a` is a subtype of `b`.
    pub fn is_subtype(&mut self, a: ItemKind, b: ItemKind) -> Result<()> {
        if self.cache.contains(&(a, b)) {
            return Ok(());
        }

        let mut is_subtype = |a, b| match (a, b) {
            (ItemKind::Resource(a), ItemKind::Resource(b)) => self.resource(a, b),
            (ItemKind::Type(a), ItemKind::Type(b)) => self.ty(a, b),
            (ItemKind::Func(a), ItemKind::Func(b)) => self.func(a, b),
            (ItemKind::Instance(a), ItemKind::Instance(b)) => self.interface(a, b),
            (ItemKind::Instantiation(a), ItemKind::Instantiation(b)) => {
                let a = &self.definitions.worlds[self.packages[a].world];
                let b = &self.definitions.worlds[self.packages[b].world];
                self.instance_exports(&a.exports, &b.exports)
            }
            (ItemKind::Instantiation(a), ItemKind::Instance(b)) => {
                let a = &self.definitions.worlds[self.packages[a].world];
                let b = &self.definitions.interfaces[b];
                self.instance_exports(&a.exports, &b.exports)
            }
            (ItemKind::Instance(a), ItemKind::Instantiation(b)) => {
                let a = &self.definitions.interfaces[a];
                let b = &self.definitions.worlds[self.packages[b].world];
                self.instance_exports(&a.exports, &b.exports)
            }
            (ItemKind::Component(a), ItemKind::Component(b)) => self.world(a, b),
            (ItemKind::Module(a), ItemKind::Module(b)) => self.module(a, b),
            (ItemKind::Value(a), ItemKind::Value(b)) => self.value_type(a, b),
            _ => {
                let (expected, found) = self.expected_found(&a, &b);
                bail!(
                    "expected {expected}, found {found}",
                    expected = expected.as_str(self.definitions),
                    found = found.as_str(self.definitions)
                )
            }
        };

        let result = is_subtype(a, b);
        if result.is_ok() {
            self.cache.insert((a, b));
        }

        result
    }

    fn expected_found<'b, T>(&self, a: &'b T, b: &'b T) -> (&'b T, &'b T) {
        match self.kind() {
            // For covariant checks, the supertype is the expected type
            SubtypeCheckKind::Covariant => (b, a),
            // For contravariant checks, the subtype is the expected type
            SubtypeCheckKind::Contravariant => (a, b),
        }
    }

    /// Gets the current check kind.
    fn kind(&self) -> SubtypeCheckKind {
        self.kinds
            .last()
            .copied()
            .unwrap_or(SubtypeCheckKind::Covariant)
    }

    /// Inverts the current check kind.
    pub(crate) fn invert(&mut self) -> SubtypeCheckKind {
        let prev = self.kind();
        self.kinds.push(match prev {
            SubtypeCheckKind::Covariant => SubtypeCheckKind::Contravariant,
            SubtypeCheckKind::Contravariant => SubtypeCheckKind::Covariant,
        });
        prev
    }

    /// Reverts to the previous check kind.
    pub(crate) fn revert(&mut self) {
        self.kinds.pop().expect("mismatched stack");
    }

    fn resource(&self, a: ResourceId, b: ResourceId) -> Result<()> {
        if a == b {
            return Ok(());
        }

        let a = self.definitions.resolve_resource(a);
        let b = self.definitions.resolve_resource(b);
        if a.name != b.name {
            let (expected, found) = self.expected_found(a, b);

            bail!(
                "expected resource `{expected}`, found resource `{found}`",
                expected = expected.name,
                found = found.name
            );
        }

        Ok(())
    }

    fn ty(&mut self, a: Type, b: Type) -> Result<()> {
        match (a, b) {
            (Type::Func(a), Type::Func(b)) => return self.func(a, b),
            (Type::Value(a), Type::Value(b)) => return self.value_type(a, b),
            (Type::Interface(a), Type::Interface(b)) => return self.interface(a, b),
            (Type::World(a), Type::World(b)) => return self.world(a, b),
            (Type::Module(a), Type::Module(b)) => return self.module(a, b),
            _ => {}
        }

        let (expected, found) = self.expected_found(&a, &b);

        bail!(
            "expected {expected}, found {found}",
            expected = expected.as_str(self.definitions),
            found = found.as_str(self.definitions)
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
            let (expected, found) = self.expected_found(a, b);
            bail!(
                "expected function with parameter count {expected}, found parameter count {found}",
                expected = expected.params.len(),
                found = found.params.len(),
            );
        }

        for (i, ((an, a), (bn, b))) in a.params.iter().zip(b.params.iter()).enumerate() {
            if an != bn {
                let (expected, found) = self.expected_found(an, bn);
                bail!("expected function parameter {i} to be named `{expected}`, found name `{found}`");
            }

            self.value_type(*a, *b)
                .with_context(|| format!("mismatched type for function parameter `{bn}`"))?;
        }

        match (&a.results, &b.results) {
            (None, None) => return Ok(()),
            (Some(FuncResult::Scalar(a)), Some(FuncResult::Scalar(b))) => {
                return self
                    .value_type(*a, *b)
                    .context("mismatched type for function result");
            }
            (Some(FuncResult::List(a)), Some(FuncResult::List(b))) => {
                for (i, ((an, a), (bn, b))) in a.iter().zip(b.iter()).enumerate() {
                    if an != bn {
                        let (expected, found) = self.expected_found(an, bn);
                        bail!("expected function result {i} to be named `{expected}`, found name `{found}`");
                    }

                    self.value_type(*a, *b)
                        .with_context(|| format!("mismatched type for function result `{bn}`"))?;
                }

                return Ok(());
            }
            (Some(FuncResult::List(_)), Some(FuncResult::Scalar(_)))
            | (Some(FuncResult::Scalar(_)), Some(FuncResult::List(_)))
            | (Some(_), None)
            | (None, Some(_)) => {
                // Handle the mismatch below
            }
        }

        let (expected, found) = self.expected_found(a, b);
        match (&expected.results, &found.results) {
            (Some(FuncResult::List(_)), Some(FuncResult::Scalar(_))) => {
                bail!("expected function that returns a named result, found function with a single result type")
            }
            (Some(FuncResult::Scalar(_)), Some(FuncResult::List(_))) => {
                bail!("expected function that returns a single result type, found function that returns a named result")
            }
            (Some(_), None) => {
                bail!("expected function with a result, found function without a result")
            }
            (None, Some(_)) => {
                bail!("expected function without a result, found function with a result")
            }
            (Some(FuncResult::Scalar(_)), Some(FuncResult::Scalar(_)))
            | (Some(FuncResult::List(_)), Some(FuncResult::List(_)))
            | (None, None) => unreachable!(),
        }
    }

    fn instance_exports(
        &mut self,
        a: &IndexMap<String, ItemKind>,
        b: &IndexMap<String, ItemKind>,
    ) -> Result<()> {
        // For instance type subtyping, all exports in the other
        // instance type must be present in this instance type's
        // exports (i.e. it can export *more* than what this instance
        // type needs).
        for (k, b) in b.iter() {
            match a.get(k) {
                Some(a) => {
                    self.is_subtype(*a, *b)
                        .with_context(|| format!("mismatched type for export `{k}`"))?;
                }
                None => match self.kind() {
                    SubtypeCheckKind::Covariant => {
                        bail!(
                            "instance is missing expected {kind} export `{k}`",
                            kind = b.as_str(self.definitions)
                        )
                    }
                    SubtypeCheckKind::Contravariant => {
                        bail!(
                            "instance has unexpected {kind} export `{k}`",
                            kind = b.as_str(self.definitions)
                        )
                    }
                },
            }
        }

        Ok(())
    }

    fn interface(&mut self, a: InterfaceId, b: InterfaceId) -> Result<()> {
        if a == b {
            return Ok(());
        }

        let a = &self.definitions.interfaces[a];
        let b = &self.definitions.interfaces[b];
        self.instance_exports(&a.exports, &b.exports)
    }

    fn world(&mut self, a: WorldId, b: WorldId) -> Result<()> {
        let a = &self.definitions.worlds[a];
        let b = &self.definitions.worlds[b];

        // For component type subtyping, all exports in the other component
        // type must be present in this component type's exports (i.e. it
        // can export *more* than what this component type needs).
        // However, for imports, the check is reversed (i.e. it is okay
        // to import *less* than what this component type needs).
        let prev = self.invert();
        for (k, a) in a.imports.iter() {
            match b.imports.get(k) {
                Some(b) => {
                    self.is_subtype(*b, *a)
                        .with_context(|| format!("mismatched type for import `{k}`"))?;
                }
                None => match prev {
                    SubtypeCheckKind::Covariant => {
                        bail!(
                            "component is missing expected {kind} import `{k}`",
                            kind = a.as_str(self.definitions)
                        )
                    }
                    SubtypeCheckKind::Contravariant => {
                        bail!(
                            "component has unexpected import {kind} `{k}`",
                            kind = a.as_str(self.definitions)
                        )
                    }
                },
            }
        }

        self.revert();

        for (k, b) in b.exports.iter() {
            match a.exports.get(k) {
                Some(a) => {
                    self.is_subtype(*a, *b)
                        .with_context(|| format!("mismatched type for export `{k}`"))?;
                }
                None => match prev {
                    SubtypeCheckKind::Covariant => {
                        bail!(
                            "component is missing expected {kind} export `{k}`",
                            kind = b.as_str(self.definitions)
                        )
                    }
                    SubtypeCheckKind::Contravariant => {
                        bail!(
                            "component has unexpected {kind} export `{k}`",
                            kind = b.as_str(self.definitions)
                        )
                    }
                },
            }
        }

        Ok(())
    }

    fn module(&mut self, a: ModuleId, b: ModuleId) -> Result<()> {
        if a == b {
            return Ok(());
        }

        let a = &self.definitions.modules[a];
        let b = &self.definitions.modules[b];

        let prev = self.invert();

        // For module type subtyping, all exports in the other module
        // type must be present in expected module type's exports (i.e. it
        // can export *more* than what is expected module type needs).
        // However, for imports, the check is reversed (i.e. it is okay
        // to import *less* than what this module type needs).
        for (k, a) in a.imports.iter() {
            match b.imports.get(k) {
                Some(b) => {
                    self.core_extern(b, a).with_context(|| {
                        format!("mismatched type for import `{m}::{n}`", m = k.0, n = k.1)
                    })?;
                }
                None => match prev {
                    SubtypeCheckKind::Covariant => bail!(
                        "module is missing expected {a} import `{m}::{n}`",
                        m = k.0,
                        n = k.1
                    ),
                    SubtypeCheckKind::Contravariant => {
                        bail!(
                            "module has unexpected {a} import `{m}::{n}`",
                            m = k.0,
                            n = k.1
                        )
                    }
                },
            }
        }

        for (k, b) in b.exports.iter() {
            match a.exports.get(k) {
                Some(a) => {
                    self.core_extern(a, b)
                        .with_context(|| format!("mismatched type for export `{k}`"))?;
                }
                None => match prev {
                    SubtypeCheckKind::Covariant => {
                        bail!("module is missing expected {b} export `{k}`")
                    }
                    SubtypeCheckKind::Contravariant => {
                        bail!("module has unexpected {b} export `{k}`")
                    }
                },
            }
        }

        Ok(())
    }

    fn core_extern(&self, a: &CoreExtern, b: &CoreExtern) -> Result<()> {
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
            (CoreExtern::Func(a), CoreExtern::Func(b)) => return self.core_func(a, b),
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
                    let (expected, found) = self.expected_found(ae, be);
                    bail!("expected table element type {expected}, found {found}");
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
                    val_type: at,
                    mutable: am,
                },
                CoreExtern::Global {
                    val_type: bt,
                    mutable: bm,
                },
            ) => {
                if am != bm {
                    bail!("mismatched mutable flag for globals");
                }

                if at != bt {
                    let (expected, found) = self.expected_found(at, bt);
                    bail!("expected global type {expected}, found {found}");
                }

                return Ok(());
            }
            (CoreExtern::Tag(a), CoreExtern::Tag(b)) => return self.core_func(a, b),
            _ => {}
        }

        let (expected, found) = self.expected_found(a, b);
        bail!("expected {expected}, found {found}");
    }

    fn core_func(&self, a: &CoreFunc, b: &CoreFunc) -> Result<()> {
        if a != b {
            let (expected, found) = self.expected_found(a, b);
            bail!("expected {expected}, found {found}");
        }

        Ok(())
    }

    fn value_type(&self, a: ValueType, b: ValueType) -> Result<()> {
        let a = self.definitions.resolve_type(a);
        let b = self.definitions.resolve_type(b);

        match (a, b) {
            (ValueType::Primitive(a), ValueType::Primitive(b)) => self.primitive(a, b),
            (ValueType::Defined { id: a, .. }, ValueType::Defined { id: b, .. }) => {
                self.defined_type(a, b)
            }
            (ValueType::Borrow(a), ValueType::Borrow(b))
            | (ValueType::Own(a), ValueType::Own(b)) => self.resource(a, b),
            _ => {
                let (expected, found) = self.expected_found(&a, &b);
                bail!(
                    "expected {expected}, found {found}",
                    expected = expected.as_str(self.definitions),
                    found = found.as_str(self.definitions)
                )
            }
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

        let a = &self.definitions.types[a];
        let b = &self.definitions.types[b];
        match (a, b) {
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
            (DefinedType::Variant(a), DefinedType::Variant(b)) => self.variant(a, b),
            (DefinedType::Record(a), DefinedType::Record(b)) => self.record(a, b),
            (DefinedType::Flags(a), DefinedType::Flags(b)) => self.flags(a, b),
            (DefinedType::Enum(a), DefinedType::Enum(b)) => self.enum_type(a, b),
            (DefinedType::Alias(_), _) | (_, DefinedType::Alias(_)) => {
                unreachable!("aliases should have been resolved")
            }
            _ => {
                let (expected, found) = self.expected_found(a, b);
                bail!(
                    "expected {expected}, found {found}",
                    expected = expected.as_str(self.definitions),
                    found = found.as_str(self.definitions)
                )
            }
        }
    }

    fn result(&self, desc: &str, a: &Option<ValueType>, b: &Option<ValueType>) -> Result<()> {
        match (a, b) {
            (None, None) => return Ok(()),
            (Some(a), Some(b)) => {
                return self
                    .value_type(*a, *b)
                    .with_context(|| format!("mismatched type for result `{desc}`"))
            }
            (Some(_), None) | (None, Some(_)) => {
                // Handle mismatch below
            }
        }

        let (expected, found) = self.expected_found(a, b);
        match (expected, found) {
            (None, None) | (Some(_), Some(_)) => unreachable!(),
            (Some(_), None) => bail!("expected an `{desc}` for result type"),
            (None, Some(_)) => bail!("expected no `{desc}` for result type"),
        }
    }

    fn enum_type(&self, a: &Enum, b: &Enum) -> Result<()> {
        if a.0.len() != b.0.len() {
            let (expected, found) = self.expected_found(a, b);
            bail!(
                "expected an enum type case count of {expected}, found a count of {found}",
                expected = expected.0.len(),
                found = found.0.len()
            );
        }

        if let Some((index, (a, b))) =
            a.0.iter()
                .zip(b.0.iter())
                .enumerate()
                .find(|(_, (a, b))| a != b)
        {
            let (expected, found) = self.expected_found(a, b);
            bail!("expected enum case {index} to be named `{expected}`, found an enum case named `{found}`");
        }

        Ok(())
    }

    fn flags(&self, a: &Flags, b: &Flags) -> Result<()> {
        if a.0.len() != b.0.len() {
            let (expected, found) = self.expected_found(a, b);
            bail!(
                "expected a flags type flag count of {expected}, found a count of {found}",
                expected = expected.0.len(),
                found = found.0.len()
            );
        }

        if let Some((index, (a, b))) =
            a.0.iter()
                .zip(b.0.iter())
                .enumerate()
                .find(|(_, (a, b))| a != b)
        {
            let (expected, found) = self.expected_found(a, b);
            bail!("expected flag {index} to be named `{expected}`, found a flag named `{found}`");
        }

        Ok(())
    }

    fn record(&self, a: &Record, b: &Record) -> Result<()> {
        if a.fields.len() != b.fields.len() {
            let (expected, found) = self.expected_found(a, b);
            bail!(
                "expected a record field count of {expected}, found a count of {found}",
                expected = expected.fields.len(),
                found = found.fields.len()
            );
        }

        for (i, ((an, a), (bn, b))) in a.fields.iter().zip(b.fields.iter()).enumerate() {
            if an != bn {
                let (expected, found) = self.expected_found(an, bn);
                bail!("expected record field {i} to be named `{expected}`, found a field named `{found}`");
            }

            self.value_type(*a, *b)
                .with_context(|| format!("mismatched type for record field `{bn}`"))?;
        }

        Ok(())
    }

    fn variant(&self, a: &Variant, b: &Variant) -> Result<()> {
        if a.cases.len() != b.cases.len() {
            let (expected, found) = self.expected_found(a, b);
            bail!(
                "expected a variant case count of {expected}, found a count of {found}",
                expected = expected.cases.len(),
                found = found.cases.len()
            );
        }

        for (i, ((an, a), (bn, b))) in a.cases.iter().zip(b.cases.iter()).enumerate() {
            if an != bn {
                let (expected, found) = self.expected_found(an, bn);
                bail!("expected variant case {i} to be named `{expected}`, found a case named `{found}`");
            }

            match (a, b) {
                (None, None) => {}
                (Some(a), Some(b)) => self
                    .value_type(*a, *b)
                    .with_context(|| format!("mismatched type for variant case `{bn}`"))?,
                _ => {
                    let (expected, found) = self.expected_found(a, b);
                    match (expected, found) {
                        (None, None) | (Some(_), Some(_)) => unreachable!(),
                        (None, Some(_)) => {
                            bail!("expected variant case `{bn}` to be untyped, found a typed case")
                        }
                        (Some(_), None) => {
                            bail!("expected variant case `{bn}` to be typed, found an untyped case")
                        }
                    }
                }
            }
        }

        Ok(())
    }

    fn tuple(&self, a: &Vec<ValueType>, b: &Vec<ValueType>) -> Result<()> {
        if a.len() != b.len() {
            let (expected, found) = self.expected_found(a, b);
            bail!(
                "expected a tuple of size {expected}, found a tuple of size {found}",
                expected = expected.len(),
                found = found.len()
            );
        }

        for (i, (a, b)) in a.iter().zip(b.iter()).enumerate() {
            self.value_type(*a, *b)
                .with_context(|| format!("mismatched type for tuple item {i}"))?;
        }

        Ok(())
    }

    fn primitive(&self, a: PrimitiveType, b: PrimitiveType) -> Result<()> {
        // Note: currently subtyping for primitive types is done in terms of equality
        // rather than actual subtyping; the reason for this is that implementing
        // runtimes don't yet support more complex subtyping rules.
        if a != b {
            let (expected, found) = self.expected_found(&a, &b);
            bail!(
                "expected {expected}, found {found}",
                expected = expected.as_str(),
                found = found.as_str()
            );
        }

        Ok(())
    }
}
