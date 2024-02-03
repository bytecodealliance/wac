use super::{
    parse_delimited, parse_token, Ident, Lookahead, PackageName, Parse, ParseResult, Peek,
};
use crate::lexer::{Lexer, Token};
use miette::SourceSpan;
use serde::Serialize;

/// Represents an expression in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Expr<'a> {
    /// The span of the entire expression.
    pub span: SourceSpan,
    /// The primary expression.
    pub primary: PrimaryExpr<'a>,
    /// The postfix expressions
    pub postfix: Vec<PostfixExpr<'a>>,
}

impl<'a> Parse<'a> for Expr<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        let primary = PrimaryExpr::parse(lexer)?;

        // Currently, only the access expressions are supported for postfix expressions.
        // As they have the same precedence, we don't need to perform climbing.
        let mut postfix = Vec::new();
        while let Some((Ok(token), _)) = lexer.peek() {
            match token {
                Token::Dot => {
                    postfix.push(PostfixExpr::Access(Parse::parse(lexer)?));
                }
                Token::OpenBracket => {
                    postfix.push(PostfixExpr::NamedAccess(Parse::parse(lexer)?));
                }
                _ => break,
            }
        }

        let start = primary.span();
        let len = postfix.last().map_or(start.len(), |p| {
            p.span().offset() + p.span().len() - start.offset()
        });

        Ok(Self {
            span: SourceSpan::new(start.offset().into(), len.into()),
            primary,
            postfix,
        })
    }
}

/// Represents a primary expression in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum PrimaryExpr<'a> {
    /// A new expression.
    New(NewExpr<'a>),
    /// A nested expression.
    Nested(NestedExpr<'a>),
    /// An identifier.
    Ident(Ident<'a>),
}

impl PrimaryExpr<'_> {
    /// Gets the span of the primary expression.
    pub fn span(&self) -> SourceSpan {
        match self {
            PrimaryExpr::New(new) => new.span,
            PrimaryExpr::Nested(nested) => nested.span,
            PrimaryExpr::Ident(ident) => ident.span,
        }
    }
}

impl<'a> Parse<'a> for PrimaryExpr<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        let mut lookahead = Lookahead::new(lexer);
        if NewExpr::peek(&mut lookahead) {
            Ok(Self::New(Parse::parse(lexer)?))
        } else if NestedExpr::peek(&mut lookahead) {
            Ok(Self::Nested(Parse::parse(lexer)?))
        } else if Ident::peek(&mut lookahead) {
            Ok(Self::Ident(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

/// Represents a new expression in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct NewExpr<'a> {
    /// The span of the new expression.
    pub span: SourceSpan,
    /// The package name in the expression.
    pub package: PackageName<'a>,
    /// The instantiation arguments in the expression.
    pub arguments: Vec<InstantiationArgument<'a>>,
}

impl<'a> Parse<'a> for NewExpr<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        let start = parse_token(lexer, Token::NewKeyword)?;
        let package = PackageName::parse(lexer)?;
        parse_token(lexer, Token::OpenBrace)?;
        let arguments = parse_delimited(lexer, Token::CloseBrace, true)?;
        let end = parse_token(lexer, Token::CloseBrace)?;
        Ok(Self {
            span: SourceSpan::new(
                start.offset().into(),
                ((end.offset() + end.len()) - start.offset()).into(),
            ),
            package,
            arguments,
        })
    }
}

impl Peek for NewExpr<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::NewKeyword)
    }
}

/// Represents an instantiation argument in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum InstantiationArgument<'a> {
    /// The argument name is inferred.
    Inferred(Ident<'a>),
    /// The argument is a spread of an instance.
    Spread(Ident<'a>),
    /// The argument is a named instantiation argument.
    Named(NamedInstantiationArgument<'a>),
    /// Fill remaining arguments with implicit imports.
    Fill(SourceSpan),
}

impl<'a> Parse<'a> for InstantiationArgument<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        let mut lookahead = Lookahead::new(lexer);
        if lookahead.peek(Token::Ellipsis) {
            // This is a spread of an instance or a fill.
            let span = parse_token(lexer, Token::Ellipsis)?;
            match lexer.peek() {
                Some((Ok(Token::Comma), _)) | Some((Ok(Token::CloseBrace), _)) => {
                    // This is a fill.
                    Ok(Self::Fill(span))
                }
                _ => {
                    // This is a spread of an instance.
                    Ok(Self::Spread(Parse::parse(lexer)?))
                }
            }
        } else if NamedInstantiationArgument::peek(&mut lookahead) {
            // Peek again to see if this is really a named instantiation argument or
            // an inferred argument.
            if let Some((Ok(Token::Colon), _)) = lexer.peek2() {
                Ok(Self::Named(Parse::parse(lexer)?))
            } else {
                Ok(Self::Inferred(Parse::parse(lexer)?))
            }
        } else {
            Err(lookahead.error())
        }
    }
}

impl Peek for InstantiationArgument<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::Ellipsis) | NamedInstantiationArgument::peek(lookahead)
    }
}

/// Represents a named instantiation argument in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct NamedInstantiationArgument<'a> {
    /// The name of the argument.
    pub name: InstantiationArgumentName<'a>,
    /// The expression in the argument.
    pub expr: Expr<'a>,
}

impl<'a> Parse<'a> for NamedInstantiationArgument<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        let name = Parse::parse(lexer)?;
        parse_token(lexer, Token::Colon)?;
        let expr = Parse::parse(lexer)?;
        Ok(Self { name, expr })
    }
}

impl Peek for NamedInstantiationArgument<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        InstantiationArgumentName::peek(lookahead)
    }
}

/// Represents the argument name in an instantiation argument in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum InstantiationArgumentName<'a> {
    /// The argument name is an identifier.
    Ident(Ident<'a>),
    /// The argument name is a string.
    String(super::String<'a>),
}

impl InstantiationArgumentName<'_> {
    /// Gets the string value of the instantiation argument name.
    pub fn as_str(&self) -> &str {
        match self {
            Self::Ident(ident) => ident.string,
            Self::String(string) => string.value,
        }
    }
}

impl<'a> Parse<'a> for InstantiationArgumentName<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        let mut lookahead = Lookahead::new(lexer);
        if Ident::peek(&mut lookahead) {
            Ok(Self::Ident(Parse::parse(lexer)?))
        } else if super::String::peek(&mut lookahead) {
            Ok(Self::String(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

impl Peek for InstantiationArgumentName<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        Ident::peek(lookahead) || super::String::peek(lookahead)
    }
}

impl<'a> InstantiationArgumentName<'a> {
    /// Gets the span of the instantiation argument name.
    pub fn span(&self) -> SourceSpan {
        match self {
            Self::Ident(ident) => ident.span,
            Self::String(string) => string.span,
        }
    }
}

/// Represents a nested expression in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct NestedExpr<'a> {
    /// The span of the nested expression.
    pub span: SourceSpan,
    /// The inner expression.
    pub inner: Box<Expr<'a>>,
}

impl<'a> Parse<'a> for NestedExpr<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        let start = parse_token(lexer, Token::OpenParen)?;
        let inner = Box::new(Parse::parse(lexer)?);
        let end = parse_token(lexer, Token::CloseParen)?;
        Ok(Self {
            span: SourceSpan::new(
                start.offset().into(),
                ((end.offset() + end.len()) - start.offset()).into(),
            ),
            inner,
        })
    }
}

impl Peek for NestedExpr<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::OpenParen)
    }
}

/// Represents a postfix expression in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum PostfixExpr<'a> {
    /// The postfix expression is an access expression.
    Access(AccessExpr<'a>),
    /// The postfix expression is a named access expression.
    NamedAccess(NamedAccessExpr<'a>),
}

impl<'a> PostfixExpr<'a> {
    /// Gets the span of the postfix expression.
    pub fn span(&self) -> SourceSpan {
        match self {
            PostfixExpr::Access(access) => access.span,
            PostfixExpr::NamedAccess(access) => access.span,
        }
    }
}

/// Represents an access expression in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AccessExpr<'a> {
    /// The span of the access expression.
    pub span: SourceSpan,
    /// The identifier in the expression.
    pub id: Ident<'a>,
}

impl<'a> Parse<'a> for AccessExpr<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        let start = parse_token(lexer, Token::Dot)?;
        let id: Ident = Parse::parse(lexer)?;
        Ok(Self {
            span: SourceSpan::new(
                start.offset().into(),
                (id.span.offset() - start.offset() + id.span.len()).into(),
            ),
            id,
        })
    }
}

impl Peek for AccessExpr<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::Dot)
    }
}

/// Represents a named access expression in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct NamedAccessExpr<'a> {
    /// The span of the access expression.
    pub span: SourceSpan,
    /// The name string in the expression.
    pub string: super::String<'a>,
}

impl<'a> Parse<'a> for NamedAccessExpr<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        let opening = parse_token(lexer, Token::OpenBracket)?;
        let string = Parse::parse(lexer)?;
        let closing = parse_token(lexer, Token::CloseBracket)?;
        Ok(Self {
            span: SourceSpan::new(
                opening.offset().into(),
                ((closing.offset() + closing.len()) - opening.offset()).into(),
            ),
            string,
        })
    }
}

impl Peek for NamedAccessExpr<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::OpenBracket)
    }
}
