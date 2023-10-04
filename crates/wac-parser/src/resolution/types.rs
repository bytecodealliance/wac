use super::{serialize_arena, serialize_id, serialize_optional_id, ScopeId};
use id_arena::{Arena, Id};
use indexmap::{IndexMap, IndexSet};
use serde::Serialize;
use std::fmt;

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

/// Represents the various type definitions.
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

/// Represent the kind of an external type.
#[derive(Debug, Clone, Copy, Serialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub enum ExternType {
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

impl fmt::Display for ExternType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Func(_) => write!(f, "function type"),
            Self::Value(_) => write!(f, "value type"),
            Self::Interface(_) => write!(f, "interface"),
            Self::World(_) => write!(f, "world"),
            Self::Module(_) => write!(f, "module type"),
        }
    }
}

/// Represents the kind of an external item.
#[derive(Debug, Clone, Copy, Serialize, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub enum ExternKind {
    /// The kind is a type.
    Type(ExternType),
    /// The kind is a function.
    Func(#[serde(serialize_with = "serialize_id")] FuncId),
    /// The kind is a component instance.
    Instance(#[serde(serialize_with = "serialize_id")] InterfaceId),
    /// The kind is a component.
    Component(#[serde(serialize_with = "serialize_id")] WorldId),
    /// The kind is a core module type.
    Module(#[serde(serialize_with = "serialize_id")] ModuleId),
    /// The kind is a value.
    Value(Type),
}

impl fmt::Display for ExternKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Func(_) => write!(f, "function"),
            Self::Type(t) => write!(f, "{t}"),
            Self::Instance(_) => write!(f, "instance"),
            Self::Component(_) => write!(f, "component"),
            Self::Module(_) => write!(f, "module type"),
            Self::Value(_) => write!(f, "value"),
        }
    }
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
    Kind(ExternKind),
}

impl Extern {
    /// Gets the extern kind of the item.
    pub fn kind(&self) -> ExternKind {
        match self {
            Self::Use { ty, .. } => ExternKind::Type(ExternType::Value(*ty)),
            Self::Kind(kind) => *kind,
        }
    }
}

/// Represents a map of extern items.
pub type ExternMap = IndexMap<String, Extern>;

/// Represents a primitive type.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Serialize)]
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
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Type {
    /// A primitive type.
    Primitive(PrimitiveType),
    /// A defined value type.
    Defined(DefinedTypeId),
}

impl Serialize for Type {
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
    Tuple(Vec<Type>),
    /// A list type.
    List(Type),
    /// An option type.
    Option(Type),
    /// A result type.
    Result {
        /// The result's `ok` type.
        ok: Option<Type>,
        /// The result's `err` type.
        err: Option<Type>,
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
    Alias(Type),
}

/// Represents a resource method.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ResourceMethod {
    /// The resource method is a constructor.
    Constructor(#[serde(serialize_with = "serialize_id")] FuncId),
    /// The resource method is a static method.
    Static {
        /// The name of the static method.
        name: String,
        /// The type of the static method.
        #[serde(serialize_with = "serialize_id")]
        ty: FuncId,
    },
    /// The resource method is an instance method.
    Instance {
        /// The name of the instance method.
        name: String,
        /// The type of the instance method.
        #[serde(serialize_with = "serialize_id")]
        ty: FuncId,
    },
}

/// Represents a resource type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Resource {
    /// The resource methods.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub methods: Vec<ResourceMethod>,
}

/// Represents a variant.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Variant {
    /// The variant cases.
    pub cases: IndexMap<String, Option<Type>>,
}

/// Represents a record type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Record {
    /// The record fields.
    pub fields: IndexMap<String, Type>,
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
    pub params: IndexMap<String, Type>,
    /// The results of the function.
    pub results: Option<FuncResult>,
}

/// Represents a function result.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum FuncResult {
    /// A scalar result.
    Scalar(Type),
    /// A list of named results.
    List(IndexMap<String, Type>),
}

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
