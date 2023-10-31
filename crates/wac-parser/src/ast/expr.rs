use super::{
    display, parse_delimited, parse_optional, parse_token, Ident, Lookahead, PackageName, Parse,
    ParseResult, Peek,
};
use crate::lexer::{Lexer, Span, Token};
use serde::Serialize;

/// Represents an expression in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Expr<'a> {
    /// The primary expression.
    pub primary: PrimaryExpr<'a>,
    /// The postfix expressions
    pub postfix: Vec<PostfixExpr<'a>>,
}

impl<'a> Parse<'a> for Expr<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let primary = Parse::parse(lexer)?;
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
        Ok(Self { primary, postfix })
    }
}

display!(Expr, expr);

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

impl<'a> Parse<'a> for PrimaryExpr<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
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
    /// The package name in the expression.
    pub package: PackageName<'a>,
    /// The instantiation arguments in the expression.
    pub arguments: Vec<InstantiationArgument<'a>>,
    /// Whether or not a trailing ellipsis was in the expression.
    pub ellipsis: bool,
}

impl<'a> Parse<'a> for NewExpr<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        parse_token(lexer, Token::NewKeyword)?;
        let package = PackageName::parse(lexer)?;
        parse_token(lexer, Token::OpenBrace)?;
        let arguments = parse_delimited(lexer, &[Token::CloseBrace, Token::Ellipsis], true)?;
        let ellipsis = parse_optional(lexer, Token::Ellipsis, |_| Ok(true))?.unwrap_or(false);
        parse_token(lexer, Token::CloseBrace)?;
        Ok(Self {
            package,
            arguments,
            ellipsis,
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
    /// The argument is a named instantiation argument.
    Named(NamedInstantiationArgument<'a>),
    /// The argument is an identifier.
    Ident(Ident<'a>),
}

impl<'a> Parse<'a> for InstantiationArgument<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead = Lookahead::new(lexer);
        if NamedInstantiationArgument::peek(&mut lookahead) {
            // Peek again to see if this is really a named instantiation argument.
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

impl Peek for InstantiationArgument<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        NamedInstantiationArgument::peek(lookahead)
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
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
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

impl<'a> Parse<'a> for InstantiationArgumentName<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
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
    pub fn span(&self) -> Span<'a> {
        match self {
            Self::Ident(ident) => ident.span,
            Self::String(string) => string.span,
        }
    }
}

/// Represents a nested expression in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct NestedExpr<'a>(pub Box<Expr<'a>>);

impl<'a> Parse<'a> for NestedExpr<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        parse_token(lexer, Token::OpenParen)?;
        let expr = Box::new(Parse::parse(lexer)?);
        parse_token(lexer, Token::CloseParen)?;
        Ok(Self(expr))
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
    pub fn span(&self) -> Span<'a> {
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
    pub span: Span<'a>,
    /// The identifier in the expression.
    pub id: Ident<'a>,
}

impl<'a> Parse<'a> for AccessExpr<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut span = parse_token(lexer, Token::Dot)?;
        let id: Ident = Parse::parse(lexer)?;
        span.end = id.span.end;
        Ok(Self { span, id })
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
    pub span: Span<'a>,
    /// The name string in the expression.
    pub string: super::String<'a>,
}

impl<'a> Parse<'a> for NamedAccessExpr<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut span = parse_token(lexer, Token::OpenBracket)?;
        let string = Parse::parse(lexer)?;
        let closing = parse_token(lexer, Token::CloseBracket)?;
        span.end = closing.end;
        Ok(Self { span, string })
    }
}

impl Peek for NamedAccessExpr<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::OpenBracket)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::test::roundtrip;

    #[test]
    fn primary_expr_roundtrip() {
        roundtrip::<Expr>("x", "x").unwrap();
        roundtrip::<Expr>("y.x.z", "y.x.z").unwrap();
        roundtrip::<Expr>("y[\"x\"][\"z\"]", "y[\"x\"][\"z\"]").unwrap();
        roundtrip::<Expr>("foo[\"bar\"].baz[\"qux\"]", "foo[\"bar\"].baz[\"qux\"]").unwrap();
        roundtrip::<Expr>("(foo-bar-baz)", "(foo-bar-baz)").unwrap();
        roundtrip::<Expr>("new foo:bar {}", "new foo:bar {}").unwrap();
        roundtrip::<Expr>(
            "new foo:bar { foo, \"bar\": (new baz:qux {...}), \"baz\": foo[\"baz\"].qux }",
            "new foo:bar {\n    foo,\n    \"bar\": (new baz:qux { ... }),\n    \"baz\": foo[\"baz\"].qux,\n}",
        )
        .unwrap();
    }
}
