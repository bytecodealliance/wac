use super::{
    display, parse_delimited, parse_optional, parse_token, DocComment, Error, Ident, Lookahead,
    PackagePath, Parse, ParseResult, Peek,
};
use crate::lexer::{Lexer, Span, Token};
use serde::Serialize;

/// Represents a type statement in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum TypeStatement<'a> {
    /// The statement is for an interface declaration.
    Interface(InterfaceDecl<'a>),
    /// The statement is for a world declaration.
    World(WorldDecl<'a>),
    /// The statement is for a type declaration.
    Type(TypeDecl<'a>),
}

impl<'a> Parse<'a> for TypeStatement<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead = Lookahead::new(lexer);
        if InterfaceDecl::peek(&mut lookahead) {
            Ok(Self::Interface(Parse::parse(lexer)?))
        } else if WorldDecl::peek(&mut lookahead) {
            Ok(Self::World(Parse::parse(lexer)?))
        } else if TypeDecl::peek(&mut lookahead) {
            Ok(Self::Type(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Peek for TypeStatement<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::InterfaceKeyword)
            || lookahead.peek(Token::WorldKeyword)
            || TypeDecl::peek(lookahead)
    }
}

display!(TypeStatement, type_statement);

/// Represents a top-level type declaration in the AST.
///
/// Unlike tin interfaces and worlds, resources cannot
/// be declared at the top-level.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum TypeDecl<'a> {
    /// The declaration is for a variant.
    Variant(VariantDecl<'a>),
    /// The declaration is for a record.
    Record(RecordDecl<'a>),
    /// The declaration is for a flags.
    Flags(FlagsDecl<'a>),
    /// The declaration is for an enum.
    Enum(EnumDecl<'a>),
    /// The declaration is for a type alias.
    Alias(TypeAlias<'a>),
}

impl TypeDecl<'_> {
    /// Gets the identifier of the type being declared.
    pub fn id(&self) -> &Ident {
        match self {
            Self::Variant(variant) => &variant.id,
            Self::Record(record) => &record.id,
            Self::Flags(flags) => &flags.id,
            Self::Enum(e) => &e.id,
            Self::Alias(alias) => &alias.id,
        }
    }
}

impl<'a> Parse<'a> for TypeDecl<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead = Lookahead::new(lexer);
        if lookahead.peek(Token::VariantKeyword) {
            Ok(Self::Variant(Parse::parse(lexer)?))
        } else if lookahead.peek(Token::RecordKeyword) {
            Ok(Self::Record(Parse::parse(lexer)?))
        } else if lookahead.peek(Token::FlagsKeyword) {
            Ok(Self::Flags(Parse::parse(lexer)?))
        } else if lookahead.peek(Token::EnumKeyword) {
            Ok(Self::Enum(Parse::parse(lexer)?))
        } else if lookahead.peek(Token::TypeKeyword) {
            Ok(Self::Alias(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Peek for TypeDecl<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::VariantKeyword)
            || lookahead.peek(Token::RecordKeyword)
            || lookahead.peek(Token::FlagsKeyword)
            || lookahead.peek(Token::EnumKeyword)
            || lookahead.peek(Token::TypeKeyword)
    }
}

/// Represents a resource declaration in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ResourceDecl<'a> {
    /// The doc comments for the resource.
    pub docs: Vec<DocComment<'a>>,
    /// The identifier of the resource.
    pub id: Ident<'a>,
    /// The methods of the resource.
    pub methods: Vec<ResourceMethod<'a>>,
}

impl<'a> Parse<'a> for ResourceDecl<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::ResourceKeyword)?;
        let id = Ident::parse(lexer)?;
        let mut lookahead = Lookahead::new(lexer);
        let methods = if lookahead.peek(Token::Semicolon) {
            lexer.next();
            Default::default()
        } else if lookahead.peek(Token::OpenBrace) {
            parse_token(lexer, Token::OpenBrace)?;
            let methods = parse_delimited(lexer, &[Token::CloseBrace], false)?;
            parse_token(lexer, Token::CloseBrace)?;
            methods
        } else {
            return Err(lookahead.error());
        };

        Ok(Self { docs, id, methods })
    }
}

/// Represents a variant declaration in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct VariantDecl<'a> {
    /// The doc comments for the variant.
    pub docs: Vec<DocComment<'a>>,
    /// The identifier of the variant.
    pub id: Ident<'a>,
    /// The cases of the variant.
    pub cases: Vec<VariantCase<'a>>,
}

impl<'a> Parse<'a> for VariantDecl<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::VariantKeyword)?;
        let id = Ident::parse(lexer)?;
        parse_token(lexer, Token::OpenBrace)?;
        let cases = parse_delimited(lexer, &[Token::CloseBrace], true)?;
        let close = parse_token(lexer, Token::CloseBrace)?;

        if cases.is_empty() {
            return Err(Error::EmptyType {
                ty: "variant",
                kind: "case",
                span: close,
            });
        }

        Ok(Self { docs, id, cases })
    }
}

/// Represents a variant case in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct VariantCase<'a> {
    /// The doc comments for the case.
    pub docs: Vec<DocComment<'a>>,
    /// The identifier of the case.
    pub id: Ident<'a>,
    /// The type of the case.
    pub ty: Option<Type<'a>>,
}

impl<'a> Parse<'a> for VariantCase<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        let id = Ident::parse(lexer)?;
        let ty = parse_optional(lexer, Token::OpenParen, |lexer| {
            let ty = Parse::parse(lexer)?;
            parse_token(lexer, Token::CloseParen)?;
            Ok(ty)
        })?;
        Ok(Self { docs, id, ty })
    }
}

impl Peek for VariantCase<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::Ident)
    }
}

/// Represents a record declaration in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct RecordDecl<'a> {
    /// The doc comments for the record.
    pub docs: Vec<DocComment<'a>>,
    /// The identifier of the record.
    pub id: Ident<'a>,
    /// The fields of the record.
    pub fields: Vec<Field<'a>>,
}

impl<'a> Parse<'a> for RecordDecl<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::RecordKeyword)?;
        let id = Ident::parse(lexer)?;
        parse_token(lexer, Token::OpenBrace)?;
        let fields = parse_delimited(lexer, &[Token::CloseBrace], true)?;
        let close = parse_token(lexer, Token::CloseBrace)?;

        if fields.is_empty() {
            return Err(Error::EmptyType {
                ty: "record",
                kind: "field",
                span: close,
            });
        }

        Ok(Self { docs, id, fields })
    }
}

/// Represents a record field in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Field<'a> {
    /// The docs for the field.
    pub docs: Vec<DocComment<'a>>,
    /// The identifier of the field.
    pub id: Ident<'a>,
    /// The type of the field.
    pub ty: Type<'a>,
}

impl<'a> Parse<'a> for Field<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        let named: NamedType = Parse::parse(lexer)?;
        Ok(Self {
            docs,
            id: named.id,
            ty: named.ty,
        })
    }
}

impl Peek for Field<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        NamedType::peek(lookahead)
    }
}

/// Represents a flags declaration in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FlagsDecl<'a> {
    /// The doc comments for the flags.
    pub docs: Vec<DocComment<'a>>,
    /// The identifier of the flags.
    pub id: Ident<'a>,
    /// The flag values.
    pub flags: Vec<Flag<'a>>,
}

impl<'a> Parse<'a> for FlagsDecl<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::FlagsKeyword)?;
        let id = Ident::parse(lexer)?;
        parse_token(lexer, Token::OpenBrace)?;
        let flags = parse_delimited(lexer, &[Token::CloseBrace], true)?;
        let close = parse_token(lexer, Token::CloseBrace)?;

        if flags.is_empty() {
            return Err(Error::EmptyType {
                ty: "flags",
                kind: "flag",
                span: close,
            });
        }

        Ok(Self { docs, id, flags })
    }
}

/// Represents a flag in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Flag<'a> {
    /// The doc comments for the flag.
    pub docs: Vec<DocComment<'a>>,
    /// The identifier of the flag.
    pub id: Ident<'a>,
}

impl<'a> Parse<'a> for Flag<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        let id = Ident::parse(lexer)?;
        Ok(Self { docs, id })
    }
}

impl Peek for Flag<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::Ident)
    }
}

/// Represents an enum declaration in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EnumDecl<'a> {
    /// The doc comments for the enum.
    pub docs: Vec<DocComment<'a>>,
    /// The identifier of the enum.
    pub id: Ident<'a>,
    /// The cases of the enum.
    pub cases: Vec<EnumCase<'a>>,
}

impl<'a> Parse<'a> for EnumDecl<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::EnumKeyword)?;
        let id = Ident::parse(lexer)?;
        parse_token(lexer, Token::OpenBrace)?;
        let cases = parse_delimited(lexer, &[Token::CloseBrace], true)?;
        let close = parse_token(lexer, Token::CloseBrace)?;

        if cases.is_empty() {
            return Err(Error::EmptyType {
                ty: "enum",
                kind: "case",
                span: close,
            });
        }

        Ok(Self { docs, id, cases })
    }
}

/// Represents an enum case in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct EnumCase<'a> {
    /// The doc comments for the enum case.
    pub docs: Vec<DocComment<'a>>,
    /// The identifier of the enum case.
    pub id: Ident<'a>,
}

impl<'a> Parse<'a> for EnumCase<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        let id = Ident::parse(lexer)?;
        Ok(Self { docs, id })
    }
}

impl Peek for EnumCase<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::Ident)
    }
}

/// Represents a resource method in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ResourceMethod<'a> {
    /// The method is a constructor.
    Constructor(Constructor<'a>),
    /// The method is a instance or static method.
    Method(Method<'a>),
}

impl<'a> Parse<'a> for ResourceMethod<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead = Lookahead::new(lexer);
        if lookahead.peek(Token::ConstructorKeyword) {
            Ok(Self::Constructor(Parse::parse(lexer)?))
        } else if Ident::peek(&mut lookahead) {
            Ok(Self::Method(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Peek for ResourceMethod<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::ConstructorKeyword) || Ident::peek(lookahead)
    }
}

/// Represents a resource constructor in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Constructor<'a> {
    /// The doc comments for the constructor.
    pub docs: Vec<DocComment<'a>>,
    /// The span of the constructor keyword.
    pub span: Span<'a>,
    /// The parameters of the constructor.
    pub params: Vec<NamedType<'a>>,
}

impl<'a> Parse<'a> for Constructor<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        let span = parse_token(lexer, Token::ConstructorKeyword)?;
        parse_token(lexer, Token::OpenParen)?;
        let params = parse_delimited(lexer, &[Token::CloseParen], true)?;
        parse_token(lexer, Token::CloseParen)?;
        parse_token(lexer, Token::Semicolon)?;
        Ok(Self { docs, span, params })
    }
}

/// Represents a resource method in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Method<'a> {
    /// The doc comments for the method.
    pub docs: Vec<DocComment<'a>>,
    /// The identifier of the method.
    pub id: Ident<'a>,
    /// Wether or not the method is static.
    pub is_static: bool,
    /// The function type of the method.
    pub ty: FuncType<'a>,
}

impl<'a> Parse<'a> for Method<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        let id = Ident::parse(lexer)?;
        parse_token(lexer, Token::Colon)?;
        let is_static = lexer
            .peek()
            .map(|(r, _)| matches!(r, Ok(Token::StaticKeyword)))
            .unwrap_or(false);

        if is_static {
            lexer.next();
        }

        let ty = Parse::parse(lexer)?;
        parse_token(lexer, Token::Semicolon)?;
        Ok(Self {
            docs,
            id,
            is_static,
            ty,
        })
    }
}

/// Represents a function type reference in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum FuncTypeRef<'a> {
    /// The reference is a function type.
    Func(FuncType<'a>),
    /// The reference is an identifier to a function type.
    Ident(Ident<'a>),
}

impl<'a> Parse<'a> for FuncTypeRef<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead = Lookahead::new(lexer);
        if lookahead.peek(Token::FuncKeyword) {
            Ok(Self::Func(Parse::parse(lexer)?))
        } else if Ident::peek(&mut lookahead) {
            Ok(Self::Ident(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

/// Represents a function type in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct FuncType<'a> {
    /// The parameters of the function.
    pub params: Vec<NamedType<'a>>,
    /// The results of the function.
    pub results: ResultList<'a>,
}

impl<'a> Parse<'a> for FuncType<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        parse_token(lexer, Token::FuncKeyword)?;
        parse_token(lexer, Token::OpenParen)?;
        let params = parse_delimited(lexer, &[Token::CloseParen], true)?;
        parse_token(lexer, Token::CloseParen)?;
        let results =
            parse_optional(lexer, Token::Arrow, Parse::parse)?.unwrap_or(ResultList::Empty);

        Ok(Self { params, results })
    }
}

impl Peek for FuncType<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::FuncKeyword)
    }
}

/// Represents a result list in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ResultList<'a> {
    /// The function has no results.
    Empty,
    /// The function returns a scalar value.
    Scalar(Type<'a>),
    /// The function has named results.
    Named(Vec<NamedType<'a>>),
}

impl<'a> Parse<'a> for ResultList<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead = Lookahead::new(lexer);
        if lookahead.peek(Token::OpenParen) {
            parse_token(lexer, Token::OpenParen)?;
            let results = parse_delimited(lexer, &[Token::CloseParen], true)?;
            parse_token(lexer, Token::CloseParen)?;
            Ok(Self::Named(results))
        } else if Type::peek(&mut lookahead) {
            Ok(Self::Scalar(Parse::parse(lexer)?))
        } else {
            Ok(Self::Empty)
        }
    }
}

/// Represents a name and an associated type in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct NamedType<'a> {
    /// The identifier of the type.
    pub id: Ident<'a>,
    /// The type.
    pub ty: Type<'a>,
}

impl<'a> Parse<'a> for NamedType<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let id = Ident::parse(lexer)?;
        parse_token(lexer, Token::Colon)?;
        let ty = Parse::parse(lexer)?;
        Ok(Self { id, ty })
    }
}

impl Peek for NamedType<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        Ident::peek(lookahead)
    }
}

/// Represents a type alias in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TypeAlias<'a> {
    /// The docs for the type alias.
    pub docs: Vec<DocComment<'a>>,
    /// The identifier of the type alias.
    pub id: Ident<'a>,
    /// The kind of type alias.
    pub kind: TypeAliasKind<'a>,
}

impl<'a> Parse<'a> for TypeAlias<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::TypeKeyword)?;
        let id = Ident::parse(lexer)?;
        parse_token(lexer, Token::Equals)?;
        let kind = Parse::parse(lexer)?;
        parse_token(lexer, Token::Semicolon)?;
        Ok(Self { docs, id, kind })
    }
}

/// Represents a type alias kind in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum TypeAliasKind<'a> {
    /// The alias is to a function type.
    Func(FuncType<'a>),
    /// The alias is to another type.
    Type(Type<'a>),
}

impl<'a> Parse<'a> for TypeAliasKind<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead = Lookahead::new(lexer);
        if lookahead.peek(Token::FuncKeyword) {
            Ok(Self::Func(Parse::parse(lexer)?))
        } else if Type::peek(&mut lookahead) {
            Ok(Self::Type(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

/// Represents a type in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum Type<'a> {
    /// A `u8` type.
    U8(Span<'a>),
    /// A `s8` type.
    S8(Span<'a>),
    /// A `u16` type.
    U16(Span<'a>),
    /// A `s16` type.
    S16(Span<'a>),
    /// A `u32` type.
    U32(Span<'a>),
    /// A `s32` type.
    S32(Span<'a>),
    /// A `u64` type.
    U64(Span<'a>),
    /// A `s64` type.
    S64(Span<'a>),
    /// A `float32` type.
    Float32(Span<'a>),
    /// A `float64` type.
    Float64(Span<'a>),
    /// A `char` type.
    Char(Span<'a>),
    /// A `bool` type.
    Bool(Span<'a>),
    /// A `string` type.
    String(Span<'a>),
    /// A tuple type.
    Tuple(Vec<Type<'a>>, Span<'a>),
    /// A list type.
    List(Box<Type<'a>>, Span<'a>),
    /// An option type.
    Option(Box<Type<'a>>, Span<'a>),
    /// A result type.
    Result {
        /// The `ok` of the result type.
        ok: Option<Box<Type<'a>>>,
        /// The `err` of the result type.
        err: Option<Box<Type<'a>>>,
        /// The span of the result type.
        span: Span<'a>,
    },
    /// A borrow type.
    Borrow(Ident<'a>, Span<'a>),
    /// An identifier to a value type.
    Ident(Ident<'a>),
}

impl<'a> Type<'a> {
    /// Gets the span of the type.
    pub fn span(&self) -> Span<'a> {
        match self {
            Self::U8(span)
            | Self::S8(span)
            | Self::U16(span)
            | Self::S16(span)
            | Self::U32(span)
            | Self::S32(span)
            | Self::U64(span)
            | Self::S64(span)
            | Self::Float32(span)
            | Self::Float64(span)
            | Self::Char(span)
            | Self::Bool(span)
            | Self::String(span)
            | Self::Tuple(_, span)
            | Self::List(_, span)
            | Self::Option(_, span)
            | Self::Result { span, .. }
            | Self::Borrow(_, span) => *span,
            Self::Ident(ident) => ident.span,
        }
    }
}

impl<'a> Parse<'a> for Type<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead = Lookahead::new(lexer);
        if lookahead.peek(Token::U8Keyword) {
            Ok(Self::U8(lexer.next().unwrap().1))
        } else if lookahead.peek(Token::S8Keyword) {
            Ok(Self::S8(lexer.next().unwrap().1))
        } else if lookahead.peek(Token::U16Keyword) {
            Ok(Self::U16(lexer.next().unwrap().1))
        } else if lookahead.peek(Token::S16Keyword) {
            Ok(Self::S16(lexer.next().unwrap().1))
        } else if lookahead.peek(Token::U32Keyword) {
            Ok(Self::U32(lexer.next().unwrap().1))
        } else if lookahead.peek(Token::S32Keyword) {
            Ok(Self::S32(lexer.next().unwrap().1))
        } else if lookahead.peek(Token::U64Keyword) {
            Ok(Self::U64(lexer.next().unwrap().1))
        } else if lookahead.peek(Token::S64Keyword) {
            Ok(Self::S64(lexer.next().unwrap().1))
        } else if lookahead.peek(Token::Float32Keyword) {
            Ok(Self::Float32(lexer.next().unwrap().1))
        } else if lookahead.peek(Token::Float64Keyword) {
            Ok(Self::Float64(lexer.next().unwrap().1))
        } else if lookahead.peek(Token::CharKeyword) {
            Ok(Self::Char(lexer.next().unwrap().1))
        } else if lookahead.peek(Token::BoolKeyword) {
            Ok(Self::Bool(lexer.next().unwrap().1))
        } else if lookahead.peek(Token::StringKeyword) {
            Ok(Self::String(lexer.next().unwrap().1))
        } else if lookahead.peek(Token::TupleKeyword) {
            let mut span = lexer.next().unwrap().1;
            parse_token(lexer, Token::OpenAngle)?;

            // There must be at least one type in the tuple.
            let mut lookahead = Lookahead::new(lexer);
            if !Type::peek(&mut lookahead) {
                return Err(lookahead.error());
            }

            let types = parse_delimited(lexer, &[Token::CloseAngle], true)?;
            assert!(!types.is_empty());
            let close = parse_token(lexer, Token::CloseAngle)?;
            span.end = close.end;
            Ok(Self::Tuple(types, span))
        } else if lookahead.peek(Token::ListKeyword) {
            let mut span = lexer.next().unwrap().1;
            parse_token(lexer, Token::OpenAngle)?;
            let ty = Box::new(Parse::parse(lexer)?);
            let close = parse_token(lexer, Token::CloseAngle)?;
            span.end = close.end;
            Ok(Self::List(ty, span))
        } else if lookahead.peek(Token::OptionKeyword) {
            let mut span = lexer.next().unwrap().1;
            parse_token(lexer, Token::OpenAngle)?;
            let ty = Box::new(Parse::parse(lexer)?);
            let close = parse_token(lexer, Token::CloseAngle)?;
            span.end = close.end;
            Ok(Self::Option(ty, span))
        } else if lookahead.peek(Token::ResultKeyword) {
            let mut span = lexer.next().unwrap().1;
            let (ok, err) = match parse_optional(lexer, Token::OpenAngle, |lexer| {
                let mut lookahead = Lookahead::new(lexer);
                let ok = if lookahead.peek(Token::Underscore) {
                    lexer.next();
                    None
                } else if Type::peek(&mut lookahead) {
                    Some(Box::new(Parse::parse(lexer)?))
                } else {
                    return Err(lookahead.error());
                };

                let err = parse_optional(lexer, Token::Comma, |lexer| {
                    let mut lookahead = Lookahead::new(lexer);
                    if lookahead.peek(Token::Underscore) {
                        lexer.next();
                        Ok(None)
                    } else if Type::peek(&mut lookahead) {
                        Ok(Some(Box::new(Parse::parse(lexer)?)))
                    } else {
                        return Err(lookahead.error());
                    }
                })?
                .unwrap_or(None);

                let close = parse_token(lexer, Token::CloseAngle)?;
                span.end = close.end;
                Ok((ok, err))
            })? {
                Some((ok, err)) => (ok, err),
                None => (None, None),
            };
            Ok(Self::Result { ok, err, span })
        } else if lookahead.peek(Token::BorrowKeyword) {
            let mut span = lexer.next().unwrap().1;
            parse_token(lexer, Token::OpenAngle)?;
            let id = Parse::parse(lexer)?;
            let close = parse_token(lexer, Token::CloseAngle)?;
            span.end = close.end;
            Ok(Self::Borrow(id, span))
        } else if Ident::peek(&mut lookahead) {
            Ok(Self::Ident(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Peek for Type<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::U8Keyword)
            || lookahead.peek(Token::S8Keyword)
            || lookahead.peek(Token::U16Keyword)
            || lookahead.peek(Token::S16Keyword)
            || lookahead.peek(Token::U32Keyword)
            || lookahead.peek(Token::S32Keyword)
            || lookahead.peek(Token::U64Keyword)
            || lookahead.peek(Token::S64Keyword)
            || lookahead.peek(Token::Float32Keyword)
            || lookahead.peek(Token::Float64Keyword)
            || lookahead.peek(Token::CharKeyword)
            || lookahead.peek(Token::BoolKeyword)
            || lookahead.peek(Token::StringKeyword)
            || lookahead.peek(Token::TupleKeyword)
            || lookahead.peek(Token::ListKeyword)
            || lookahead.peek(Token::OptionKeyword)
            || lookahead.peek(Token::ResultKeyword)
            || lookahead.peek(Token::BorrowKeyword)
            || Ident::peek(lookahead)
    }
}

/// Represents an interface or world type declaration in the AST.
///
/// Unlike top-level type declarations, interfaces and worlds can
/// also declare resources.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ItemTypeDecl<'a> {
    /// The declaration is for a resource.
    Resource(ResourceDecl<'a>),
    /// The declaration is for a variant.
    Variant(VariantDecl<'a>),
    /// The declaration is for a record.
    Record(RecordDecl<'a>),
    /// The declaration is for a flags.
    Flags(FlagsDecl<'a>),
    /// The declaration is for an enum.
    Enum(EnumDecl<'a>),
    /// The declaration is for a type alias.
    Alias(TypeAlias<'a>),
}

impl<'a> Parse<'a> for ItemTypeDecl<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead = Lookahead::new(lexer);
        if lookahead.peek(Token::ResourceKeyword) {
            Ok(Self::Resource(Parse::parse(lexer)?))
        } else if lookahead.peek(Token::VariantKeyword) {
            Ok(Self::Variant(Parse::parse(lexer)?))
        } else if lookahead.peek(Token::RecordKeyword) {
            Ok(Self::Record(Parse::parse(lexer)?))
        } else if lookahead.peek(Token::FlagsKeyword) {
            Ok(Self::Flags(Parse::parse(lexer)?))
        } else if lookahead.peek(Token::EnumKeyword) {
            Ok(Self::Enum(Parse::parse(lexer)?))
        } else if lookahead.peek(Token::TypeKeyword) {
            Ok(Self::Alias(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Peek for ItemTypeDecl<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::ResourceKeyword)
            || lookahead.peek(Token::VariantKeyword)
            || lookahead.peek(Token::RecordKeyword)
            || lookahead.peek(Token::FlagsKeyword)
            || lookahead.peek(Token::EnumKeyword)
            || lookahead.peek(Token::TypeKeyword)
    }
}

impl ItemTypeDecl<'_> {
    /// Gets the identifier of the type being declared.
    pub fn id(&self) -> &Ident {
        match self {
            Self::Resource(resource) => &resource.id,
            Self::Variant(variant) => &variant.id,
            Self::Record(record) => &record.id,
            Self::Flags(flags) => &flags.id,
            Self::Enum(e) => &e.id,
            Self::Alias(alias) => &alias.id,
        }
    }
}

/// Represents an interface declaration in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InterfaceDecl<'a> {
    /// The doc comments for the interface.
    pub docs: Vec<DocComment<'a>>,
    /// The identifier of the interface.
    pub id: Ident<'a>,
    /// The items of the interface.
    pub items: Vec<InterfaceItem<'a>>,
}

impl<'a> Parse<'a> for InterfaceDecl<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::InterfaceKeyword)?;
        let id = Ident::parse(lexer)?;
        parse_token(lexer, Token::OpenBrace)?;
        let items = parse_delimited(lexer, &[Token::CloseBrace], false)?;
        parse_token(lexer, Token::CloseBrace)?;
        Ok(Self { docs, id, items })
    }
}

impl Peek for InterfaceDecl<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::InterfaceKeyword)
    }
}

display!(InterfaceDecl, interface_decl);

/// Represents an interface item in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum InterfaceItem<'a> {
    /// The item is a use of other types.
    Use(Box<Use<'a>>),
    /// The item is a type declaration.
    Type(ItemTypeDecl<'a>),
    /// The item is an interface export.
    Export(InterfaceExport<'a>),
}

impl<'a> Parse<'a> for InterfaceItem<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead = Lookahead::new(lexer);
        if Use::peek(&mut lookahead) {
            Ok(Self::Use(Box::new(Parse::parse(lexer)?)))
        } else if InterfaceExport::peek(&mut lookahead) {
            Ok(Self::Export(Parse::parse(lexer)?))
        } else if ItemTypeDecl::peek(&mut lookahead) {
            Ok(Self::Type(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Peek for InterfaceItem<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        Use::peek(lookahead) || InterfaceExport::peek(lookahead) || ItemTypeDecl::peek(lookahead)
    }
}

/// Represents a "use" in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Use<'a> {
    /// The doc comments for the use.
    pub docs: Vec<DocComment<'a>>,
    /// The path to the interface or world being used.
    pub path: UsePath<'a>,
    /// The items being used.
    pub items: Vec<UseItem<'a>>,
}

impl<'a> Parse<'a> for Use<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::UseKeyword)?;
        let path = Parse::parse(lexer)?;
        parse_token(lexer, Token::Dot)?;
        parse_token(lexer, Token::OpenBrace)?;
        let items = parse_delimited(lexer, &[Token::CloseBrace], true)?;
        parse_token(lexer, Token::CloseBrace)?;
        parse_token(lexer, Token::Semicolon)?;
        Ok(Self { docs, path, items })
    }
}

impl Peek for Use<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::UseKeyword)
    }
}

/// Represents a use path in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum UsePath<'a> {
    /// The path is a package path.
    Package(PackagePath<'a>),
    /// The path is an identifier.
    Ident(Ident<'a>),
}

impl<'a> Parse<'a> for UsePath<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead: Lookahead<'_> = Lookahead::new(lexer);
        if PackagePath::peek(&mut lookahead) {
            Ok(Self::Package(Parse::parse(lexer)?))
        } else if Ident::peek(&mut lookahead) {
            Ok(Self::Ident(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Peek for UsePath<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        PackagePath::peek(lookahead) | Ident::peek(lookahead)
    }
}

/// Represents a use item in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct UseItem<'a> {
    /// The identifier of the item.
    pub id: Ident<'a>,
    /// The optional `as` identifier of the item.
    pub as_id: Option<Ident<'a>>,
}

impl<'a> Parse<'a> for UseItem<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let id = Ident::parse(lexer)?;
        let as_id = parse_optional(lexer, Token::AsKeyword, Ident::parse)?;
        Ok(Self { id, as_id })
    }
}

impl Peek for UseItem<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        Ident::peek(lookahead)
    }
}

/// Represents an interface export in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InterfaceExport<'a> {
    /// The doc comments for the export.
    pub docs: Vec<DocComment<'a>>,
    /// The identifier of the export.
    pub id: Ident<'a>,
    /// The type of the export.
    pub ty: FuncTypeRef<'a>,
}

impl<'a> Parse<'a> for InterfaceExport<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        let id = Ident::parse(lexer)?;
        parse_token(lexer, Token::Colon)?;
        let ty = Parse::parse(lexer)?;
        parse_token(lexer, Token::Semicolon)?;
        Ok(Self { docs, id, ty })
    }
}

impl Peek for InterfaceExport<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        Ident::peek(lookahead)
    }
}

/// Represents a world declaration in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WorldDecl<'a> {
    /// The doc comments for the world.
    pub docs: Vec<DocComment<'a>>,
    /// The identifier of the world.
    pub id: Ident<'a>,
    /// The items of the world.
    pub items: Vec<WorldItem<'a>>,
}

impl<'a> Parse<'a> for WorldDecl<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::WorldKeyword)?;
        let id = Ident::parse(lexer)?;
        parse_token(lexer, Token::OpenBrace)?;
        let items = parse_delimited(lexer, &[Token::CloseBrace], false)?;
        parse_token(lexer, Token::CloseBrace)?;
        Ok(Self { docs, id, items })
    }
}

impl Peek for WorldDecl<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::WorldKeyword)
    }
}

display!(WorldDecl, world_decl);

/// Represents a world item in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum WorldItem<'a> {
    /// The item is a use.
    Use(Use<'a>),
    /// The item is a type declaration.
    Type(ItemTypeDecl<'a>),
    /// The item is a world export.
    Import(WorldImport<'a>),
    /// The item is a world export.
    Export(WorldExport<'a>),
    /// The item is a world include.
    Include(WorldInclude<'a>),
}

impl<'a> Parse<'a> for WorldItem<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead = Lookahead::new(lexer);
        if Use::peek(&mut lookahead) {
            Ok(Self::Use(Parse::parse(lexer)?))
        } else if WorldImport::peek(&mut lookahead) {
            Ok(Self::Import(Parse::parse(lexer)?))
        } else if WorldExport::peek(&mut lookahead) {
            Ok(Self::Export(Parse::parse(lexer)?))
        } else if WorldInclude::peek(&mut lookahead) {
            Ok(Self::Include(Parse::parse(lexer)?))
        } else if ItemTypeDecl::peek(&mut lookahead) {
            Ok(Self::Type(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Peek for WorldItem<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        Use::peek(lookahead)
            || WorldImport::peek(lookahead)
            || WorldExport::peek(lookahead)
            || WorldInclude::peek(lookahead)
            || ItemTypeDecl::peek(lookahead)
    }
}

/// Represents a world import in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WorldImport<'a> {
    /// The doc comments for the world import.
    pub docs: Vec<DocComment<'a>>,
    /// The path of the imported item.
    pub path: WorldItemPath<'a>,
}

impl<'a> Parse<'a> for WorldImport<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::ImportKeyword)?;
        let path = Parse::parse(lexer)?;
        parse_token(lexer, Token::Semicolon)?;
        Ok(Self { docs, path })
    }
}

impl Peek for WorldImport<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::ImportKeyword)
    }
}

/// Represents a world export in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WorldExport<'a> {
    /// The doc comments for the world export.
    pub docs: Vec<DocComment<'a>>,
    /// The path of the exported item.
    pub path: WorldItemPath<'a>,
}

impl<'a> Parse<'a> for WorldExport<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::ExportKeyword)?;
        let path = Parse::parse(lexer)?;
        parse_token(lexer, Token::Semicolon)?;
        Ok(Self { docs, path })
    }
}

impl Peek for WorldExport<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::ExportKeyword)
    }
}

/// Represents a world item path in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum WorldItemPath<'a> {
    /// The path is by name.
    Named(NamedWorldItem<'a>),
    /// The path is by a package path.
    Package(PackagePath<'a>),
    /// The path is by identifier.
    Ident(Ident<'a>),
}

impl<'a> Parse<'a> for WorldItemPath<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead = Lookahead::new(lexer);
        if PackagePath::peek(&mut lookahead) {
            Ok(Self::Package(Parse::parse(lexer)?))
        } else if Ident::peek(&mut lookahead) {
            // Peek again to see if this is a named item or an interface reference
            if let Some((Ok(Token::Colon), _)) = lexer.peek2() {
                Ok(Self::Named(Parse::parse(lexer)?))
            } else {
                Ok(Self::Ident(Parse::parse(lexer)?))
            }
        } else {
            Err(lookahead.error())
        }
    }
}

/// Represents a named world item in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct NamedWorldItem<'a> {
    /// The identifier of the item being imported or exported.
    pub id: Ident<'a>,
    /// The extern type of the item.
    pub ty: ExternType<'a>,
}

impl<'a> Parse<'a> for NamedWorldItem<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let id = Ident::parse(lexer)?;
        parse_token(lexer, Token::Colon)?;
        let ty = Parse::parse(lexer)?;
        Ok(Self { id, ty })
    }
}

/// Represents the external type of a world item in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ExternType<'a> {
    /// The type is by identifier.
    Ident(Ident<'a>),
    /// The type is an inline function type.
    Func(FuncType<'a>),
    /// The type is an inline interface.
    Interface(InlineInterface<'a>),
}

impl<'a> Parse<'a> for ExternType<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead = Lookahead::new(lexer);
        if Ident::peek(&mut lookahead) {
            Ok(Self::Ident(Parse::parse(lexer)?))
        } else if FuncType::peek(&mut lookahead) {
            Ok(Self::Func(Parse::parse(lexer)?))
        } else if InlineInterface::peek(&mut lookahead) {
            Ok(Self::Interface(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

/// Represents an inline interface in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InlineInterface<'a> {
    /// The items of the interface.
    pub items: Vec<InterfaceItem<'a>>,
}

impl<'a> Parse<'a> for InlineInterface<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        parse_token(lexer, Token::InterfaceKeyword)?;
        parse_token(lexer, Token::OpenBrace)?;
        let items = parse_delimited(lexer, &[Token::CloseBrace], false)?;
        parse_token(lexer, Token::CloseBrace)?;
        Ok(Self { items })
    }
}

impl Peek for InlineInterface<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::InterfaceKeyword)
    }
}

/// Represents a world include in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WorldInclude<'a> {
    /// The doc comments for the world include.
    pub docs: Vec<DocComment<'a>>,
    /// The reference to the world to include.
    pub world: WorldRef<'a>,
    /// The optional include-with items.
    pub with: Vec<WorldIncludeItem<'a>>,
}

impl<'a> Parse<'a> for WorldInclude<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::IncludeKeyword)?;
        let world = Parse::parse(lexer)?;
        let with = parse_optional(lexer, Token::WithKeyword, |lexer| {
            parse_token(lexer, Token::OpenBrace)?;
            let items = parse_delimited(lexer, &[Token::CloseBrace], true)?;
            parse_token(lexer, Token::CloseBrace)?;
            Ok(items)
        })?
        .unwrap_or_default();
        parse_token(lexer, Token::Semicolon)?;
        Ok(Self { docs, world, with })
    }
}

impl Peek for WorldInclude<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::IncludeKeyword)
    }
}

/// Represents a reference to a world in the AST (local or foreign).
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum WorldRef<'a> {
    /// The reference is by identifier.
    Ident(Ident<'a>),
    /// The reference is by package path.
    Package(PackagePath<'a>),
}

impl<'a> WorldRef<'a> {
    /// Gets the name of the world being referred to.
    pub fn name(&self) -> &'a str {
        match self {
            Self::Ident(id) => id.string,
            Self::Package(path) => path.span.as_str(),
        }
    }

    /// Gets the span of the world reference.
    pub fn span(&self) -> Span<'a> {
        match self {
            Self::Ident(id) => id.span,
            Self::Package(path) => path.span,
        }
    }
}

impl<'a> Parse<'a> for WorldRef<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead = Lookahead::new(lexer);
        if PackagePath::peek(&mut lookahead) {
            Ok(Self::Package(Parse::parse(lexer)?))
        } else if Ident::peek(&mut lookahead) {
            Ok(Self::Ident(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

/// Represents a renaming of an included name.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct WorldIncludeItem<'a> {
    /// The `from` name for the included item.
    pub from: Ident<'a>,
    /// The `to` name for the included item.
    pub to: Ident<'a>,
}

impl<'a> Parse<'a> for WorldIncludeItem<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let from = Ident::parse(lexer)?;
        parse_token(lexer, Token::AsKeyword)?;
        let to = Ident::parse(lexer)?;
        Ok(Self { from, to })
    }
}

impl Peek for WorldIncludeItem<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        Ident::peek(lookahead)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::test::roundtrip;

    #[test]
    fn resource_roundtrip() {
        roundtrip::<TypeStatement>(
            r#"interface i { resource foo-bar {
    /** A constructor */
    constructor(foo: u8, bar: u8);
    /// A method
    foo: func() -> string;
    /// A method
    set-foo: func(foo: string);
    /// A static method
    id: static func() -> u32;
}}"#,
            r#"interface i {
    resource foo-bar {
        /// A constructor
        constructor(foo: u8, bar: u8);

        /// A method
        foo: func() -> string;

        /// A method
        set-foo: func(foo: string);

        /// A static method
        id: static func() -> u32;
    }
}"#,
        )
        .unwrap();
    }

    #[test]
    fn variant_roundtrip() {
        roundtrip::<TypeStatement>(
            r#"variant foo {
    foo,
    bar(u32),
    baz(bar),
    qux(tuple<u8, u16, u32>)
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
            r#"type x = func(a: /* comment */ string) -> string;"#,
            r#"type x = func(a: string) -> string;"#,
        )
        .unwrap();
    }

    #[test]
    fn type_alias_roundtrip() {
        roundtrip::<TypeStatement>(
            r#"type x = tuple<u8, s8, u16, s16, u32, s32, u64, s64, float32, float64, char, bool, string, tuple<string, list<u8>>, option<list<bool>>, result, result<string>, result<_, string>, result<u8, u8>, borrow<y>, y>;"#,
            r#"type x = tuple<u8, s8, u16, s16, u32, s32, u64, s64, float32, float64, char, bool, string, tuple<string, list<u8>>, option<list<bool>>, result, result<string>, result<_, string>, result<u8, u8>, borrow<y>, y>;"#,
        )
        .unwrap();
    }

    #[test]
    fn interface_roundtrip() {
        roundtrip::<InterfaceDecl>(
            r#"interface foo {
            /// Type t
            type t = list<string>;

            /// Use x and y
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

    /// Use x and y
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

            /// Include world from package path with 2 renames.
            include foo:bar/baz with { a as a1, b as b1 };

            /// Include world from package path with 1 rename.
            include foo:bar/baz with {foo as foo1};

            /// Include world from package path (spacing).
            include foo:bar/baz with { foo as foo1 };

            /// Include world from package path newline delimited renaming.
            include foo:bar/baz with {
                foo as foo1,
                bar as bar1
            };

            /// Include local world.
            include foo-bar;

            /// Include local world with renaming.
            include foo-bar with { foo as bar };
};

include my-world;
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

    /// Include world from package path with 2 renames.
    include foo:bar/baz with {
        a as a1,
        b as b1,
    };

    /// Include world from package path with 1 rename.
    include foo:bar/baz with {
        foo as foo1,
    };

    /// Include world from package path (spacing).
    include foo:bar/baz with {
        foo as foo1,
    };

    /// Include world from package path newline delimited renaming.
    include foo:bar/baz with {
        foo as foo1,
        bar as bar1,
    };

    /// Include local world.
    include foo-bar;

    /// Include local world with renaming.
    include foo-bar with {
        foo as bar,
    };
}"#,
        )
        .unwrap();
    }
}
