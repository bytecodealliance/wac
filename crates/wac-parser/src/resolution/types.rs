use super::{serialize_id, serialize_id_map, FuncTypeId, InterfaceId, ScopeId, ValueTypeId};
use crate::ast::{
    EnumDecl, FlagsDecl, InlineInterface, InterfaceDecl, RecordDecl, ResourceDecl, TypeAlias,
    VariantDecl, WorldDecl,
};
use indexmap::{IndexMap, IndexSet};
use serde::{Serialize, Serializer};
use std::borrow::Borrow;

fn serialize_world_item_map<S>(
    map: &IndexMap<ExternName, WorldItemType>,
    serializer: S,
) -> std::result::Result<S::Ok, S::Error>
where
    S: Serializer,
{
    use serde::ser::SerializeMap;

    let mut s = serializer.serialize_map(Some(map.len()))?;
    for (k, v) in map.iter() {
        s.serialize_entry(k.as_str(), v)?;
    }
    s.end()
}

/// Represents a resolved type.
#[derive(Debug, Copy, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum Type<'a> {
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
    /// The value type is defined.
    Id(#[serde(serialize_with = "serialize_id")] ValueTypeId<'a>),
}

/// Represents a resolved value type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ValueType<'a> {
    /// A primitive type.
    Primitive(Type<'a>),
    /// A tuple type.
    Tuple(Vec<Type<'a>>),
    /// A list type.
    List(Type<'a>),
    /// An option type.
    Option(Type<'a>),
    /// A result type.
    Result {
        /// The result's `ok` type.
        ok: Option<Type<'a>>,
        /// The result's `err` type.
        err: Option<Type<'a>>,
    },
    /// A borrow type.
    ///
    /// The value type is expected to be a resource.
    Borrow(#[serde(serialize_with = "serialize_id")] ValueTypeId<'a>),
    /// The type is a resource type.
    Resource(ResourceType<'a>),
    /// The type is a variant type.
    Variant(VariantType<'a>),
    /// The type is a record type.
    Record(RecordType<'a>),
    /// The type is a flags type.
    Flags(FlagsType<'a>),
    /// The type is an enum.
    Enum(EnumType<'a>),
    /// The type is an alias to another value type.
    Alias(ValueTypeAlias<'a>),
}

/// Represents a resource method type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ResourceMethodType<'a> {
    /// The resource method is a constructor.
    Constructor(Vec<Type<'a>>),
    /// The resource method is a static method.
    Static {
        /// The name of the static method.
        name: &'a str,
        /// The type of the static method.
        #[serde(serialize_with = "serialize_id")]
        ty: FuncTypeId<'a>,
    },
    /// The resource method is an instance method.
    Instance {
        /// The name of the instance method.
        name: &'a str,
        /// The type of the instance method.
        #[serde(serialize_with = "serialize_id")]
        ty: FuncTypeId<'a>,
    },
}

/// Represents a resolved resource type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ResourceType<'a> {
    /// The resource declaration.
    #[serde(skip)]
    pub decl: &'a ResourceDecl<'a>,
    /// The resource methods.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub methods: Vec<ResourceMethodType<'a>>,
}

/// Represents a resolved variant type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct VariantType<'a> {
    /// The variant declaration.
    #[serde(skip)]
    pub decl: &'a VariantDecl<'a>,
    /// The variant cases.
    pub cases: IndexMap<&'a str, Option<Type<'a>>>,
}

/// Represents a resolved record type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RecordType<'a> {
    /// The record declaration.
    #[serde(skip)]
    pub decl: &'a RecordDecl<'a>,
    /// The record fields.
    pub fields: IndexMap<&'a str, Type<'a>>,
}

/// Represents a resolved flags type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FlagsType<'a> {
    /// The flags declaration.
    #[serde(skip)]
    pub decl: &'a FlagsDecl<'a>,
    /// The flags.
    pub flags: IndexSet<&'a str>,
}

/// Represents a resolved enum.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EnumType<'a> {
    /// The enum declaration.
    #[serde(skip)]
    pub decl: &'a EnumDecl<'a>,
    /// The enum cases.
    pub cases: IndexSet<&'a str>,
}

/// Represents an alias to another value type.
#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ValueTypeAlias<'a> {
    /// The type alias declaration.
    #[serde(skip)]
    pub alias: &'a TypeAlias<'a>,
    /// The aliased type.
    pub ty: Type<'a>,
}

/// Represents a resolved function type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FuncType<'a> {
    /// The function type declaration.
    #[serde(skip)]
    pub decl: &'a crate::ast::FuncType<'a>,
    /// The parameters of the function.
    pub params: IndexMap<&'a str, Type<'a>>,
    /// The results of the function.
    pub results: Option<ResultList<'a>>,
}

/// Represents a resolved result list.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ResultList<'a> {
    /// A single result.
    Single(Type<'a>),
    /// A list of named results.
    Named(IndexMap<&'a str, Type<'a>>),
}

/// Represents a resolved local type for interfaces and worlds.
#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum LocalType<'a> {
    /// The type is a value type.
    Type(Type<'a>),
    /// The type is a function type.
    FuncType(#[serde(serialize_with = "serialize_id")] FuncTypeId<'a>),
}

/// Represents the kind of resolved interface.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum InterfaceKind<'a> {
    /// The interface was declared.
    Declared {
        /// The interface declaration.
        #[serde(skip)]
        decl: &'a InterfaceDecl<'a>,
        /// The id of the interface.
        id: String,
    },
    /// The interface was inline.
    Inline(#[serde(skip)] &'a InlineInterface<'a>),
}

/// Represents a resolved interface type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InterfaceType<'a> {
    /// The kind of interface.
    pub kind: InterfaceKind<'a>,
    /// The types of the interface.
    pub types: IndexMap<&'a str, LocalType<'a>>,
    /// The exported functions of the interface.
    #[serde(serialize_with = "serialize_id_map")]
    pub exports: IndexMap<&'a str, FuncTypeId<'a>>,
}

/// Represents a resolved type of an world item.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum WorldItemType<'a> {
    /// The item is a function.
    Func(#[serde(serialize_with = "serialize_id")] FuncTypeId<'a>),
    /// The item is an interface.
    Interface {
        /// The interface id.
        #[serde(serialize_with = "serialize_id")]
        id: InterfaceId<'a>,
        /// The interface's scope id.
        #[serde(serialize_with = "serialize_id")]
        scope: ScopeId<'a>,
    },
}

/// Represents a resolved world type.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WorldType<'a> {
    /// The world declaration.
    #[serde(skip)]
    pub decl: &'a WorldDecl<'a>,
    /// The types of the world.
    pub types: IndexMap<&'a str, LocalType<'a>>,
    /// The imported items of the world.
    #[serde(serialize_with = "serialize_world_item_map")]
    pub imports: IndexMap<ExternName, WorldItemType<'a>>,
    /// The exported items of the world.
    #[serde(serialize_with = "serialize_world_item_map")]
    pub exports: IndexMap<ExternName, WorldItemType<'a>>,
}

/// Represents the name of a component extern item.
#[derive(Debug, Clone)]
pub enum ExternName {
    /// The extern name is a kebab-case name.
    Kebab(String),
    /// The extern name is an interface identifier.
    Interface(String),
}

impl Borrow<str> for ExternName {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl ExternName {
    /// Returns the underlying string representing this name.
    pub fn as_str(&self) -> &str {
        match self {
            Self::Kebab(name) => name,
            Self::Interface(name) => name,
        }
    }
}

impl PartialEq for ExternName {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for ExternName {}

impl std::hash::Hash for ExternName {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}
