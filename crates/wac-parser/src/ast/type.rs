use super::{
    display,
    keywords::{
        self, Bool, Enum, Export, Flags, Float32, Float64, Func, Import, Interface, Record,
        Resource, Static, Use, Variant, World, S16, S32, S64, S8, U16, U32, U64, U8,
    },
    symbols::{
        Arrow, CloseAngle, CloseBrace, CloseParen, Colon, Dot, Equals, OpenAngle, OpenBrace,
        OpenParen, Semicolon, Underscore,
    },
    AstDisplay, DocComment, Ident, Indenter, PackagePath,
};
use crate::parser::Rule;
use pest_ast::FromPest;
use std::fmt;

/// Represents a type statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::TypeStatement))]
pub enum TypeStatement<'a> {
    /// The statement is for an interface declaration.
    Interface(InterfaceDecl<'a>),
    /// The statement is for a world declaration.
    World(WorldDecl<'a>),
    /// The statement is for a resource declaration.
    Resource(ResourceDecl<'a>),
    /// The statement is for a variant declaration.
    Variant(VariantDecl<'a>),
    /// The statement is for a record declaration.
    Record(RecordDecl<'a>),
    /// The statement is for a flags declaration.
    Flags(FlagsDecl<'a>),
    /// The statement is for an enum declaration.
    Enum(EnumDecl<'a>),
    /// The statement is for a type alias.
    Alias(TypeAlias<'a>),
}

impl AstDisplay for TypeStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{indenter}")?;

        match self {
            Self::Interface(interface) => interface.fmt(f, indenter),
            Self::World(world) => world.fmt(f, indenter),
            Self::Resource(resource) => resource.fmt(f, indenter),
            Self::Variant(variant) => variant.fmt(f, indenter),
            Self::Record(record) => record.fmt(f, indenter),
            Self::Flags(flags) => flags.fmt(f, indenter),
            Self::Enum(e) => e.fmt(f, indenter),
            Self::Alias(alias) => alias.fmt(f, indenter),
        }
    }
}

display!(TypeStatement);

/// Represents a resource declaration in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::ResourceDecl))]
pub struct ResourceDecl<'a> {
    /// The `resource` keyword in the declaration.
    pub keyword: Resource<'a>,
    /// The identifier of the resource.
    pub id: Ident<'a>,
    /// The body of the resource.
    pub body: ResourceBody<'a>,
}

impl AstDisplay for ResourceDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{keyword} ", keyword = self.keyword)?;
        self.id.fmt(f, indenter)?;
        self.body.fmt(f, indenter)
    }
}

display!(ResourceDecl);

/// Represents a resource body in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::ResourceBody))]
pub enum ResourceBody<'a> {
    /// The resource body is empty.
    Empty(Semicolon<'a>),
    /// The methods of the resource body.
    Methods {
        /// The opening brace of the resource body.
        open: OpenBrace<'a>,
        /// The methods of the resource body.
        methods: Vec<(ResourceMethod<'a>, Semicolon<'a>)>,
        /// The closing brace of the resource body.
        close: CloseBrace<'a>,
    },
}

impl AstDisplay for ResourceBody<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Empty(semicolon) => write!(f, "{semicolon}"),
            Self::Methods {
                open,
                methods,
                close,
            } => {
                writeln!(f, " {open}")?;

                indenter.indent();
                for (method, semicolon) in methods {
                    write!(f, "{indenter}")?;
                    method.fmt(f, indenter)?;
                    writeln!(f, "{semicolon}")?;
                }

                indenter.dedent();
                write!(f, "{indenter}{close}")
            }
        }
    }
}

display!(ResourceBody);

/// Represents a variant declaration in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::VariantDecl))]
pub struct VariantDecl<'a> {
    /// The `variant` keyword in the declaration.
    pub keyword: Variant<'a>,
    /// The identifier of the variant.
    pub id: Ident<'a>,
    /// The body of the variant.
    pub body: VariantBody<'a>,
}

impl AstDisplay for VariantDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{keyword} ", keyword = self.keyword)?;
        self.id.fmt(f, indenter)?;
        self.body.fmt(f, indenter)
    }
}

display!(VariantDecl);

/// Represents a variant body in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::VariantBody))]
pub struct VariantBody<'a> {
    /// The opening brace of the variant body.
    pub open: OpenBrace<'a>,
    /// The cases of the variant body.
    pub cases: Vec<VariantCase<'a>>,
    /// The closing brace of the variant body.
    pub close: CloseBrace<'a>,
}

impl AstDisplay for VariantBody<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        writeln!(f, " {open}", open = self.open)?;

        indenter.indent();
        for case in &self.cases {
            write!(f, "{indenter}")?;
            case.fmt(f, indenter)?;
            writeln!(f, ",")?;
        }

        indenter.dedent();
        write!(f, "{indenter}{close}", close = self.close)
    }
}

display!(VariantBody);

/// Represents a variant case in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::VariantCase))]
pub struct VariantCase<'a> {
    /// The identifier of the case.
    pub id: Ident<'a>,
    /// The type of the case.
    pub ty: std::option::Option<VariantType<'a>>,
}

impl AstDisplay for VariantCase<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        self.id.fmt(f, indenter)?;
        if let Some(ty) = &self.ty {
            ty.fmt(f, indenter)?;
        }

        Ok(())
    }
}

display!(VariantCase);

/// Represents a variant type in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::VariantType))]
pub struct VariantType<'a> {
    /// The opening parenthesis of the variant type.
    pub open: OpenParen<'a>,
    /// The type of the variant.
    pub ty: Type<'a>,
    /// The closing parenthesis of the variant type.
    pub close: CloseParen<'a>,
}

impl AstDisplay for VariantType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{open}", open = self.open)?;
        self.ty.fmt(f, indenter)?;
        write!(f, "{close}", close = self.close)
    }
}

display!(VariantType);

/// Represents a record declaration in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::RecordDecl))]
pub struct RecordDecl<'a> {
    /// The `record` keyword in the declaration.
    pub keyword: Record<'a>,
    /// The identifier of the record.
    pub id: Ident<'a>,
    /// The body of the record.
    pub body: RecordBody<'a>,
}

impl AstDisplay for RecordDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{keyword} ", keyword = self.keyword)?;
        self.id.fmt(f, indenter)?;
        self.body.fmt(f, indenter)
    }
}

display!(RecordDecl);

/// Represents a record body in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::RecordBody))]
pub struct RecordBody<'a> {
    /// The opening brace of the record body.
    pub open: OpenBrace<'a>,
    /// The fields of the record body.
    pub fields: Vec<NamedType<'a>>,
    /// The closing brace of the record body.
    pub close: CloseBrace<'a>,
}

impl AstDisplay for RecordBody<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        writeln!(f, " {open}", open = self.open)?;

        indenter.indent();
        for field in &self.fields {
            write!(f, "{indenter}")?;
            field.fmt(f, indenter)?;
            writeln!(f, ",")?;
        }

        indenter.dedent();
        write!(f, "{indenter}{close}", close = self.close)
    }
}

display!(RecordBody);

/// Represents a flags declaration in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::FlagsDecl))]
pub struct FlagsDecl<'a> {
    /// The `flags` keyword in the declaration.
    pub keyword: Flags<'a>,
    /// The identifier of the flags.
    pub id: Ident<'a>,
    /// The body of the flags.
    pub body: FlagsBody<'a>,
}

impl AstDisplay for FlagsDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{keyword} ", keyword = self.keyword)?;
        self.id.fmt(f, indenter)?;
        self.body.fmt(f, indenter)
    }
}

display!(FlagsDecl);

/// Represents a flags body in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::FlagsBody))]
pub struct FlagsBody<'a> {
    /// The opening brace of the flags body.
    pub open: OpenBrace<'a>,
    /// The flags of the body.
    pub flags: Vec<Ident<'a>>,
    /// The closing brace of the flags body.
    pub close: CloseBrace<'a>,
}

impl AstDisplay for FlagsBody<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        writeln!(f, " {open}", open = self.open)?;

        indenter.indent();
        for flag in &self.flags {
            write!(f, "{indenter}")?;
            flag.fmt(f, indenter)?;
            writeln!(f, ",")?;
        }

        indenter.dedent();
        write!(f, "{indenter}{close}", close = self.close)
    }
}

display!(FlagsBody);

/// Represents an enum declaration in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::EnumDecl))]
pub struct EnumDecl<'a> {
    /// The `enum` keyword in the declaration.
    pub keyword: Enum<'a>,
    /// The identifier of the enum.
    pub id: Ident<'a>,
    /// The body of the enum.
    pub body: EnumBody<'a>,
}

impl AstDisplay for EnumDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{keyword} ", keyword = self.keyword)?;
        self.id.fmt(f, indenter)?;
        self.body.fmt(f, indenter)
    }
}

display!(EnumDecl);

/// Represents an enum body in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::EnumBody))]
pub struct EnumBody<'a> {
    /// The opening brace of the enum body.
    pub open: OpenBrace<'a>,
    /// The enum cases of the body.
    pub cases: Vec<Ident<'a>>,
    /// The closing brace of the enum body.
    pub close: CloseBrace<'a>,
}

impl AstDisplay for EnumBody<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        writeln!(f, " {open}", open = self.open)?;

        indenter.indent();
        for case in &self.cases {
            write!(f, "{indenter}")?;
            case.fmt(f, indenter)?;
            writeln!(f, ",")?;
        }

        indenter.dedent();
        write!(f, "{indenter}{close}", close = self.close)
    }
}

display!(EnumBody);

/// Represents a resource method in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::ResourceMethod))]
pub enum ResourceMethod<'a> {
    /// The method is a constructor.
    Constructor(Constructor<'a>),
    /// The method is a instance or static method.
    Method(Method<'a>),
}

impl AstDisplay for ResourceMethod<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Constructor(constructor) => constructor.fmt(f, indenter),
            Self::Method(method) => method.fmt(f, indenter),
        }
    }
}

display!(ResourceMethod);

/// Represents a resource constructor in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::Constructor))]
pub struct Constructor<'a> {
    /// The `constructor` keyword.
    pub keyword: keywords::Constructor<'a>,
    /// The parameters of the constructor.
    pub params: ParamList<'a>,
}

impl AstDisplay for Constructor<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{keyword}", keyword = self.keyword)?;
        self.params.fmt(f, indenter)
    }
}

display!(Constructor);

/// Represents a resource method in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::Method))]
pub struct Method<'a> {
    /// The identifier of the method.
    pub id: Ident<'a>,
    /// The colon between the identifier and the type.
    pub colon: Colon<'a>,
    /// The static keyword that is present for static methods.
    pub keyword: std::option::Option<Static<'a>>,
    /// The function type reference.
    pub func: FuncTypeRef<'a>,
}

impl AstDisplay for Method<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        self.id.fmt(f, indenter)?;
        write!(f, "{colon} ", colon = self.colon)?;

        if let Some(keyword) = &self.keyword {
            write!(f, "{keyword} ")?;
        }

        self.func.fmt(f, indenter)
    }
}

display!(Method);

/// Represents a function type reference in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::FuncTypeRef))]
pub enum FuncTypeRef<'a> {
    /// The reference is a function type.
    Func(FuncType<'a>),
    /// The reference is an identifier to a function type.
    Ident(Ident<'a>),
}

impl AstDisplay for FuncTypeRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Ident(ident) => ident.fmt(f, indenter),
            Self::Func(func) => func.fmt(f, indenter),
        }
    }
}

display!(FuncTypeRef);

/// Represents a function type in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::FuncType))]
pub struct FuncType<'a> {
    /// The `func` keyword.
    pub keyword: Func<'a>,
    /// The parameters of the function.
    pub params: ParamList<'a>,
    /// The results of the function.
    pub results: std::option::Option<ResultList<'a>>,
}

impl AstDisplay for FuncType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{keyword}", keyword = self.keyword)?;

        self.params.fmt(f, indenter)?;

        if let Some(results) = &self.results {
            write!(f, " ")?;
            results.fmt(f, indenter)?;
        }

        Ok(())
    }
}

display!(FuncType);

/// Represents a parameter list in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::ParamList))]
pub struct ParamList<'a> {
    /// The opening parenthesis of the parameter list.
    pub open: OpenParen<'a>,
    /// The parameters of the function.
    pub list: Vec<NamedType<'a>>,
    /// The closing parenthesis of the parameter list.
    pub close: CloseParen<'a>,
}

impl AstDisplay for ParamList<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{open}", open = self.open)?;

        for (i, param) in self.list.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            param.fmt(f, indenter)?;
        }

        write!(f, "{close}", close = self.close)
    }
}

display!(ParamList);

/// Represents a result list in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::ResultList))]
pub enum ResultList<'a> {
    /// The function has named results.
    Named {
        /// The arrow between the parameters and the results.
        arrow: Arrow<'a>,
        /// The results of the function.
        results: NamedResultList<'a>,
    },
    /// The function has a single result type.
    Single {
        /// The arrow between the parameters and the results.
        arrow: Arrow<'a>,
        /// The result type.
        ty: Type<'a>,
    },
}

impl AstDisplay for ResultList<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Single { arrow, ty } => {
                write!(f, "{arrow} ")?;
                ty.fmt(f, indenter)
            }
            Self::Named { arrow, results } => {
                write!(f, "{arrow} ")?;
                results.fmt(f, indenter)
            }
        }
    }
}

display!(ResultList);

/// Represents a named result list in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::NamedResultList))]
pub struct NamedResultList<'a> {
    /// The opening parenthesis of the result list.
    pub open: OpenParen<'a>,
    /// The results of the function.
    pub list: Vec<NamedType<'a>>,
    /// The closing parenthesis of the result list.
    pub close: CloseParen<'a>,
}

impl AstDisplay for NamedResultList<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{open}", open = self.open)?;

        for (i, result) in self.list.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            result.fmt(f, indenter)?;
        }

        write!(f, "{close}", close = self.close)
    }
}

display!(NamedResultList);

/// Represents a name and an associated type in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::NamedType))]
pub struct NamedType<'a> {
    /// The identifier of the type.
    pub id: Ident<'a>,
    /// The colon between the identifier and the type.
    pub colon: Colon<'a>,
    /// The type.
    pub ty: Type<'a>,
}

impl AstDisplay for NamedType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        self.id.fmt(f, indenter)?;
        write!(f, "{colon} ", colon = self.colon)?;
        self.ty.fmt(f, indenter)
    }
}

display!(NamedType);

/// Represents a type alias in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::TypeAlias))]
pub struct TypeAlias<'a> {
    /// The `type` keyword.
    pub keyword: keywords::Type<'a>,
    /// The identifier of the type alias.
    pub id: Ident<'a>,
    /// The equals sign between the identifier and the type.
    pub equals: Equals<'a>,
    /// The kind of type alias.
    pub kind: TypeAliasKind<'a>,
    /// The semicolon at the end of the type alias.
    pub semicolon: Semicolon<'a>,
}

impl AstDisplay for TypeAlias<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{keyword} ", keyword = self.keyword,)?;
        self.id.fmt(f, indenter)?;
        write!(f, " {equals} ", equals = self.equals)?;
        self.kind.fmt(f, indenter)?;
        write!(f, "{semi}", semi = self.semicolon)
    }
}

display!(TypeAlias);

/// Represents a type alias kind in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::TypeAliasKind))]
pub enum TypeAliasKind<'a> {
    /// The alias is for a function type.
    Func(FuncType<'a>),
    /// The alias is for a built-in type.
    Type(Type<'a>),
}

impl AstDisplay for TypeAliasKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Func(func) => func.fmt(f, indenter),
            Self::Type(ty) => ty.fmt(f, indenter),
        }
    }
}

display!(TypeAliasKind);

/// Represents a type in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::Type))]
pub enum Type<'a> {
    /// A `u8` type.
    U8(U8<'a>),
    /// A `s8` type.
    S8(S8<'a>),
    /// A `u16` type.
    U16(U16<'a>),
    /// A `s16` type.
    S16(S16<'a>),
    /// A `u32` type.
    U32(U32<'a>),
    /// A `s32` type.
    S32(S32<'a>),
    /// A `u64` type.
    U64(U64<'a>),
    /// A `s64` type.
    S64(S64<'a>),
    /// A `float32` type.
    Float32(Float32<'a>),
    /// A `float64` type.
    Float64(Float64<'a>),
    /// A `char` type.
    Char(super::keywords::Char<'a>),
    /// A `bool` type.
    Bool(Bool<'a>),
    /// A `string` type.
    String(super::keywords::String<'a>),
    /// A tuple type.
    Tuple(Tuple<'a>),
    /// A list type.
    List(List<'a>),
    /// An option type.
    Option(Option<'a>),
    /// A result type.
    Result(Result<'a>),
    /// A borrow type.
    Borrow(Borrow<'a>),
    /// An identifier type.
    Ident(Ident<'a>),
}

impl AstDisplay for Type<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::U8(v) => write!(f, "{v}"),
            Self::S8(v) => write!(f, "{v}"),
            Self::U16(v) => write!(f, "{v}"),
            Self::S16(v) => write!(f, "{v}"),
            Self::U32(v) => write!(f, "{v}"),
            Self::S32(v) => write!(f, "{v}"),
            Self::U64(v) => write!(f, "{v}"),
            Self::S64(v) => write!(f, "{v}"),
            Self::Float32(v) => write!(f, "{v}"),
            Self::Float64(v) => write!(f, "{v}"),
            Self::Char(v) => write!(f, "{v}"),
            Self::Bool(v) => write!(f, "{v}"),
            Self::String(v) => write!(f, "{v}"),
            Self::Tuple(tuple) => tuple.fmt(f, indenter),
            Self::List(list) => list.fmt(f, indenter),
            Self::Option(option) => option.fmt(f, indenter),
            Self::Result(result) => result.fmt(f, indenter),
            Self::Borrow(borrow) => borrow.fmt(f, indenter),
            Self::Ident(ident) => ident.fmt(f, indenter),
        }
    }
}

display!(Type);

/// Represents a tuple type in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::Tuple))]
pub struct Tuple<'a> {
    /// The `tuple` keyword.
    pub keyword: keywords::Tuple<'a>,
    /// The opening angle bracket of the tuple.
    pub open: OpenAngle<'a>,
    /// The types in the tuple.
    pub types: Vec<Type<'a>>,
    /// The closing angle bracket of the tuple.
    pub close: CloseAngle<'a>,
}

impl AstDisplay for Tuple<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(
            f,
            "{keyword}{open}",
            keyword = self.keyword,
            open = self.open
        )?;

        for (i, ty) in self.types.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            ty.fmt(f, indenter)?;
        }

        write!(f, "{close}", close = self.close)
    }
}

display!(Tuple);

/// Represents a list type in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::List))]
pub struct List<'a> {
    /// The `list` keyword.
    pub keyword: keywords::List<'a>,
    /// The opening angle bracket of the list.
    pub open: OpenAngle<'a>,
    /// The type of the list.
    pub ty: Box<Type<'a>>,
    /// The closing angle bracket of the list.
    pub close: CloseAngle<'a>,
}

impl AstDisplay for List<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(
            f,
            "{keyword}{open}",
            keyword = self.keyword,
            open = self.open
        )?;
        self.ty.fmt(f, indenter)?;
        write!(f, "{close}", close = self.close)
    }
}

display!(List);

/// Represents an option type in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::Option))]
pub struct Option<'a> {
    /// The `option` keyword.
    pub keyword: keywords::Option<'a>,
    /// The opening angle bracket of the option.
    pub open: OpenAngle<'a>,
    /// The type of the option.
    pub ty: Box<Type<'a>>,
    /// The closing angle bracket of the option.
    pub close: CloseAngle<'a>,
}

impl AstDisplay for Option<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(
            f,
            "{keyword}{open}",
            keyword = self.keyword,
            open = self.open
        )?;
        self.ty.fmt(f, indenter)?;
        write!(f, "{close}", close = self.close)
    }
}

display!(Option);

/// Represents a result type in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::Result))]
pub struct Result<'a> {
    /// The `result` keyword.
    pub keyword: keywords::Result<'a>,
    /// The specified result type.
    pub specified: std::option::Option<SpecifiedResult<'a>>,
}

impl AstDisplay for Result<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{keyword}", keyword = self.keyword)?;

        if let Some(specified) = &self.specified {
            specified.fmt(f, indenter)?;
        }

        Ok(())
    }
}

display!(Result);

/// Represents a specified result in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::SpecifiedResult))]
pub struct SpecifiedResult<'a> {
    /// The opening angle bracket of the result.
    pub open: OpenAngle<'a>,
    /// The ok type of the result.
    pub ok: OmitType<'a>,
    /// The error type of the result.
    pub err: std::option::Option<Box<Type<'a>>>,
    /// The closing angle bracket of the result.
    pub close: CloseAngle<'a>,
}

impl AstDisplay for SpecifiedResult<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{open}", open = self.open)?;

        self.ok.fmt(f, indenter)?;

        if let Some(err) = &self.err {
            write!(f, ", ")?;
            err.fmt(f, indenter)?;
        }

        write!(f, "{close}", close = self.close)
    }
}

display!(SpecifiedResult);

/// Represents a possibly omitted type in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::OmitType))]
pub enum OmitType<'a> {
    /// The type was omitted with `_`.
    Omitted(Underscore<'a>),
    /// The type was specified.
    Type(Box<Type<'a>>),
}

impl AstDisplay for OmitType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Type(ty) => ty.fmt(f, indenter),
            Self::Omitted(u) => write!(f, "{u}"),
        }
    }
}

display!(OmitType);

/// Represents a borrow type in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::Borrow))]
pub struct Borrow<'a> {
    /// The `borrow` keyword.
    pub keyword: keywords::Borrow<'a>,
    /// The opening angle bracket of the borrow.
    pub open: OpenAngle<'a>,
    /// The identifier of the borrowed type.
    pub id: Ident<'a>,
    /// The closing angle bracket of the borrow.
    pub close: CloseAngle<'a>,
}

impl AstDisplay for Borrow<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(
            f,
            "{keyword}{open}",
            keyword = self.keyword,
            open = self.open
        )?;
        self.id.fmt(f, indenter)?;
        write!(f, "{close}", close = self.close)
    }
}

display!(Borrow);

/// Represents an interface declaration in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::InterfaceDecl))]
pub struct InterfaceDecl<'a> {
    /// The `interface` keyword.
    pub keyword: Interface<'a>,
    /// The identifier of the interface.
    pub id: Ident<'a>,
    /// The body of the interface.
    pub body: InterfaceBody<'a>,
}

impl AstDisplay for InterfaceDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{indenter}{keyword} ", keyword = self.keyword)?;
        self.id.fmt(f, indenter)?;
        self.body.fmt(f, indenter)
    }
}

display!(InterfaceDecl);

/// Represents an interface body in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::InterfaceBody))]
pub struct InterfaceBody<'a> {
    /// The opening brace of the interface body.
    pub open: OpenBrace<'a>,
    /// The items of the interface body.
    pub items: Vec<InterfaceItem<'a>>,
    /// The closing brace of the interface body.
    pub close: CloseBrace<'a>,
}

impl AstDisplay for InterfaceBody<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        writeln!(f, " {open}", open = self.open)?;
        indenter.indent();

        for (i, item) in self.items.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }

            item.fmt(f, indenter)?;
            writeln!(f)?;
        }

        indenter.dedent();
        write!(f, "{indenter}{close}", close = self.close)
    }
}

display!(InterfaceBody);

/// Represents an interface item in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::InterfaceItem))]
pub struct InterfaceItem<'a> {
    /// The doc comments for the interface item.
    pub docs: Vec<DocComment<'a>>,
    /// The interface item kind.
    pub kind: InterfaceItemKind<'a>,
}

impl AstDisplay for InterfaceItem<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        for doc in &self.docs {
            doc.fmt(f, indenter)?;
        }

        self.kind.fmt(f, indenter)
    }
}

display!(InterfaceItem);

/// Represents an interface item kind in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::InterfaceItemKind))]
pub enum InterfaceItemKind<'a> {
    /// The item is a use statement.
    Use(Box<UseStatement<'a>>),
    /// The item is a type statement.
    Type(TypeStatement<'a>),
    /// The item is an interface export statement.
    Export(InterfaceExportStatement<'a>),
}

impl AstDisplay for InterfaceItemKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Use(u) => u.fmt(f, indenter),
            Self::Type(ty) => ty.fmt(f, indenter),
            Self::Export(e) => e.fmt(f, indenter),
        }
    }
}

display!(InterfaceItemKind);

/// Represents a use statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::UseStatement))]
pub struct UseStatement<'a> {
    /// The use keyword in the statement.
    pub keyword: Use<'a>,
    /// The items being used.
    pub items: UseItems<'a>,
    /// The semicolon of the export statement.
    pub semicolon: Semicolon<'a>,
}

impl AstDisplay for UseStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{indenter}{keyword} ", keyword = self.keyword)?;
        self.items.fmt(f, indenter)?;
        write!(f, "{semi}", semi = self.semicolon)
    }
}

display!(UseStatement);

/// Represents the items being used in a use statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::UseItems))]
pub struct UseItems<'a> {
    /// The path to the interface or world being used.
    pub path: UsePath<'a>,
    /// The dot in the statement.
    pub dot: Dot<'a>,
    /// The opening brace of the statement.
    pub open: OpenBrace<'a>,
    /// The items being used.
    pub items: Vec<Ident<'a>>,
    /// The closing brace of the use items.
    pub close: CloseBrace<'a>,
}

impl AstDisplay for UseItems<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        self.path.fmt(f, indenter)?;
        write!(f, "{dot}{open} ", dot = self.dot, open = self.open)?;

        for (i, item) in self.items.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            item.fmt(f, indenter)?;
        }

        write!(f, " {close}", close = self.close)
    }
}

display!(UseItems);

/// Represents a use path in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::UsePath))]
pub enum UsePath<'a> {
    /// The path is a package path.
    Package(PackagePath<'a>),
    /// The path is an identifier.
    Ident(Ident<'a>),
}

impl AstDisplay for UsePath<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Package(pkg) => pkg.fmt(f, indenter),
            Self::Ident(id) => id.fmt(f, indenter),
        }
    }
}

display!(UsePath);

/// Represents an interface export statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::InterfaceExportStatement))]
pub struct InterfaceExportStatement<'a> {
    /// The identifier of the export.
    pub id: Ident<'a>,
    /// The colon of the export statement.
    pub colon: Colon<'a>,
    /// The type of the export.
    pub ty: FuncTypeRef<'a>,
    /// The semicolon of the export statement.
    pub semicolon: Semicolon<'a>,
}

impl AstDisplay for InterfaceExportStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{indenter}")?;
        self.id.fmt(f, indenter)?;
        write!(f, "{colon} ", colon = self.colon)?;
        self.ty.fmt(f, indenter)?;
        write!(f, "{semi}", semi = self.semicolon)
    }
}

display!(InterfaceExportStatement);

/// Represents a world declaration in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldDecl))]
pub struct WorldDecl<'a> {
    /// The `world` keyword.
    pub keyword: World<'a>,
    /// The identifier of the world.
    pub id: Ident<'a>,
    /// The body of the world.
    pub body: WorldBody<'a>,
}

impl AstDisplay for WorldDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{indenter}{keyword} ", keyword = self.keyword)?;
        self.id.fmt(f, indenter)?;
        self.body.fmt(f, indenter)
    }
}

display!(WorldDecl);

/// Represents a world body in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldBody))]
pub struct WorldBody<'a> {
    /// The opening brace of the world body.
    pub open: OpenBrace<'a>,
    /// The items of the world body.
    pub items: Vec<WorldItem<'a>>,
    /// The closing brace of the world body.
    pub close: CloseBrace<'a>,
}

impl AstDisplay for WorldBody<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        writeln!(f, " {open}", open = self.open)?;
        indenter.indent();

        for (i, item) in self.items.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }

            item.fmt(f, indenter)?;
            writeln!(f)?;
        }

        indenter.dedent();
        write!(f, "{indenter}{close}", close = self.close)
    }
}

display!(WorldBody);

/// Represents a world item in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldItem))]
pub struct WorldItem<'a> {
    /// The doc comments for the world item.
    pub docs: Vec<DocComment<'a>>,
    /// The world item kind.
    pub kind: WorldItemKind<'a>,
}

impl AstDisplay for WorldItem<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        for doc in &self.docs {
            doc.fmt(f, indenter)?;
        }

        self.kind.fmt(f, indenter)
    }
}

display!(WorldItem);

/// Represents a world item kind in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldItemKind))]
pub enum WorldItemKind<'a> {
    /// The item is a use statement.
    Use(Box<UseStatement<'a>>),
    /// The item is a type statement.
    Type(TypeStatement<'a>),
    /// The item is a world export statement.
    Import(WorldImportStatement<'a>),
    /// The item is a world export statement.
    Export(WorldExportStatement<'a>),
}

impl AstDisplay for WorldItemKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Use(u) => u.fmt(f, indenter),
            Self::Type(ty) => ty.fmt(f, indenter),
            Self::Import(i) => i.fmt(f, indenter),
            Self::Export(e) => e.fmt(f, indenter),
        }
    }
}

display!(WorldItemKind);

/// Represents a world import statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldImportStatement))]
pub struct WorldImportStatement<'a> {
    /// The `import` keyword in the statement.
    pub keyword: Import<'a>,
    /// The declaration of the imported item.
    pub decl: WorldItemDecl<'a>,
    /// The semicolon of the import statement.
    pub semicolon: Semicolon<'a>,
}

impl AstDisplay for WorldImportStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{indenter}{keyword} ", keyword = self.keyword)?;
        self.decl.fmt(f, indenter)?;
        write!(f, "{semi}", semi = self.semicolon)
    }
}

display!(WorldImportStatement);

/// Represents a world export statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldExportStatement))]
pub struct WorldExportStatement<'a> {
    /// The `export` keyword in the statement.
    pub keyword: Export<'a>,
    /// The declaration of the exported item.
    pub decl: WorldItemDecl<'a>,
    /// The semicolon of the export statement.
    pub semicolon: Semicolon<'a>,
}

impl AstDisplay for WorldExportStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{indenter}{keyword} ", keyword = self.keyword)?;
        self.decl.fmt(f, indenter)?;
        write!(f, "{semi}", semi = self.semicolon)
    }
}

display!(WorldExportStatement);

/// Represents a world item declaration in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldItemDecl))]
pub enum WorldItemDecl<'a> {
    /// The declaration is by name.
    Named(WorldNamedItem<'a>),
    /// The declaration is by a reference to an interface.
    Interface(InterfaceRef<'a>),
}

impl AstDisplay for WorldItemDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Named(n) => n.fmt(f, indenter),
            Self::Interface(i) => i.fmt(f, indenter),
        }
    }
}

display!(WorldItemDecl);

/// Represents a world named item in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldNamedItem))]
pub struct WorldNamedItem<'a> {
    /// The identifier of the item being imported or exported.
    pub id: Ident<'a>,
    /// The colon between the identifier and the extern type.
    pub colon: Colon<'a>,
    /// The extern type of the item.
    pub ty: ExternType<'a>,
}

impl AstDisplay for WorldNamedItem<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        self.id.fmt(f, indenter)?;
        write!(f, "{colon} ", colon = self.colon)?;
        self.ty.fmt(f, indenter)
    }
}

display!(WorldNamedItem);

/// Represents a reference to an interface in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::InterfaceRef))]
pub enum InterfaceRef<'a> {
    /// The reference is by identifier.
    Ident(Ident<'a>),
    /// The reference is by package path.
    Path(PackagePath<'a>),
}

impl AstDisplay for InterfaceRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Ident(id) => id.fmt(f, indenter),
            Self::Path(path) => path.fmt(f, indenter),
        }
    }
}

display!(InterfaceRef);

/// Represents the external type of a world item in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::ExternType))]
pub enum ExternType<'a> {
    /// The type is by identifier.
    Ident(Ident<'a>),
    /// The type is an inline function type.
    Func(FuncType<'a>),
    /// The type is an inline interface.
    Interface(InlineInterface<'a>),
}

impl AstDisplay for ExternType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Ident(id) => id.fmt(f, indenter),
            Self::Func(func) => func.fmt(f, indenter),
            Self::Interface(interface) => interface.fmt(f, indenter),
        }
    }
}

display!(ExternType);

/// Represents an inline interface in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::InlineInterface))]
pub struct InlineInterface<'a> {
    /// The `interface` keyword in the inline interface.
    pub keyword: Interface<'a>,
    /// The body of the interface.
    pub body: InterfaceBody<'a>,
}

impl AstDisplay for InlineInterface<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{keyword}", keyword = self.keyword)?;
        self.body.fmt(f, indenter)
    }
}

display!(InlineInterface);
#[cfg(test)]
mod test {
    use super::*;
    use crate::{ast::test::roundtrip, parser::Rule};

    #[test]
    fn resource_roundtrip() {
        roundtrip::<TypeStatement>(
            Rule::TypeStatement,
            r#"resource foo-bar {
    constructor(foo: u8, bar: u8);
    foo: func() -> string;
    set-foo: func(foo: string);
    id: static func() -> u32;
    baz: x;
}"#,
            r#"resource foo-bar {
  constructor(foo: u8, bar: u8);
  foo: func() -> string;
  set-foo: func(foo: string);
  id: static func() -> u32;
  baz: x;
}"#,
        )
        .unwrap();
    }

    #[test]
    fn variant_roundtrip() {
        roundtrip::<TypeStatement>(
            Rule::TypeStatement,
            r#"variant foo {
    foo,
    bar(u32),
    baz(bar),
    qux(tuple<u8, u16, u32>),
}"#,
            r#"variant foo {
  foo,
  bar(u32),
  baz(bar),
  qux(tuple<u8, u16, u32>),
}"#,
        )
        .unwrap();
    }

    #[test]
    fn record_roundtrip() {
        roundtrip::<TypeStatement>(
            Rule::TypeStatement,
            r#"record foo-bar2-baz {
    foo: foo,
    bar-qux: list<string>,
    // A comment
    jam: borrow<foo>,
}"#,
            r#"record foo-bar2-baz {
  foo: foo,
  bar-qux: list<string>,
  jam: borrow<foo>,
}"#,
        )
        .unwrap();
    }

    #[test]
    fn flags_roundtrip() {
        roundtrip::<TypeStatement>(
            Rule::TypeStatement,
            r#"flags %flags {
    foo, bar, baz
}"#,
            r#"flags %flags {
  foo,
  bar,
  baz,
}"#,
        )
        .unwrap();
    }

    #[test]
    fn enum_roundtrip() {
        roundtrip::<TypeStatement>(
            Rule::TypeStatement,
            r#"enum foo {
    foo, bar, baz
}"#,
            r#"enum foo {
  foo,
  bar,
  baz,
}"#,
        )
        .unwrap();
    }

    #[test]
    fn func_type_alias_roundtrip() {
        roundtrip::<TypeStatement>(
            Rule::TypeStatement,
            r#"type x = func(a: /* comment */ string) -> string;"#,
            r#"type x = func(a: string) -> string;"#,
        )
        .unwrap();
    }

    #[test]
    fn type_alias_roundtrip() {
        roundtrip::<TypeStatement>(
            Rule::TypeStatement,
            r#"type x = tuple<u8, s8, u16, s16, u32, s32, u64, s64, float32, float64, char, bool, string, tuple<string, list<u8>>, option<list<bool>>, result, result<string>, result<_, string>, result<u8, u8>, borrow<y>, y>;"#,
            r#"type x = tuple<u8, s8, u16, s16, u32, s32, u64, s64, float32, float64, char, bool, string, tuple<string, list<u8>>, option<list<bool>>, result, result<string>, result<_, string>, result<u8, u8>, borrow<y>, y>;"#,
        )
        .unwrap();
    }

    #[test]
    fn interface_roundtrip() {
        roundtrip::<InterfaceDecl>(
            Rule::InterfaceDecl,
            r#"interface foo {
            /// Type t
            type t = list<string>;

            use foo.{ x, y, };

            /// Function a
            a: func(a: string, b: string) -> string;

            // not a doc comment
            type x = func() -> list<string>;
            
            /// Function b
            b: x;
}
            "#,
            r#"interface foo {
  /// Type t
  type t = list<string>;

  use foo.{ x, y };

  /// Function a
  a: func(a: string, b: string) -> string;

  type x = func() -> list<string>;

  /// Function b
  b: x;
}"#,
        )
        .unwrap();
    }

    #[test]
    fn world_roundtrip() {
        roundtrip::<WorldDecl>(
            Rule::WorldDecl,
            r#"world foo {
            /// Type t
            type t = list<string>;

            // not a doc comment
            type x = func() -> list<string>;

            use foo.{ y, };

            /// Import with function type.
            import a: func(a: string, b: string) -> string;

            /// Import with identifier.
            import b: x;

            /// Import with inline interface.
            import c: interface {
                /// Function a
                a: func(a: string, b: string) -> string;
            };

            /// Import with package path
            import foo:bar/baz@1.0.0;

            /// Export with function type.
            export a: func(a: string, b: string) -> string;

            /// Export with identifier.
            export b: x;

            /// Export with inline interface.
            export c: interface {
                /// Function a
                a: func(a: string, b: string) -> string;
            };

            /// Export with package path
            export foo:bar/baz@1.0.0;
}
            "#,
            r#"world foo {
  /// Type t
  type t = list<string>;

  type x = func() -> list<string>;

  use foo.{ y };

  /// Import with function type.
  import a: func(a: string, b: string) -> string;

  /// Import with identifier.
  import b: x;

  /// Import with inline interface.
  import c: interface {
    /// Function a
    a: func(a: string, b: string) -> string;
  };

  /// Import with package path
  import foo:bar/baz@1.0.0;

  /// Export with function type.
  export a: func(a: string, b: string) -> string;

  /// Export with identifier.
  export b: x;

  /// Export with inline interface.
  export c: interface {
    /// Function a
    a: func(a: string, b: string) -> string;
  };

  /// Export with package path
  export foo:bar/baz@1.0.0;
}"#,
        )
        .unwrap();
    }
}
