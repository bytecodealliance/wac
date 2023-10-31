use crate::lexer::{Lexer, Token};

use super::{display, parse_token, DocComment, Expr, Ident, Lookahead, Parse, ParseResult, Peek};
use serde::Serialize;

/// Represents a let statement in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct LetStatement<'a> {
    /// The doc comments for the statement.
    pub docs: Vec<DocComment<'a>>,
    /// The newly bound identifier.
    pub id: Ident<'a>,
    /// The expression being bound.
    pub expr: Expr<'a>,
}

impl<'a> Parse<'a> for LetStatement<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::LetKeyword)?;
        let id = Parse::parse(lexer)?;
        parse_token(lexer, Token::Equals)?;
        let expr = Parse::parse(lexer)?;
        parse_token(lexer, Token::Semicolon)?;
        Ok(Self { docs, id, expr })
    }
}

impl Peek for LetStatement<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::LetKeyword)
    }
}

display!(LetStatement, let_statement);

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::test::roundtrip;

    #[test]
    fn let_statement_roundtrip() {
        roundtrip::<LetStatement>("let x= y;", "let x = y;").unwrap();
        roundtrip::<LetStatement>("let x =y.x.z;", "let x = y.x.z;").unwrap();
        roundtrip::<LetStatement>("let x=y[\"x\"][\"z\"];", "let x = y[\"x\"][\"z\"];").unwrap();
        roundtrip::<LetStatement>(
            "let x = foo[\"bar\"].baz[\"qux\"];",
            "let x = foo[\"bar\"].baz[\"qux\"];",
        )
        .unwrap();

        roundtrip::<LetStatement>("let x = (y);", "let x = (y);").unwrap();

        roundtrip::<LetStatement>("let x = new foo:bar {};", "let x = new foo:bar {};").unwrap();

        roundtrip::<LetStatement>(
            "let x = new foo:bar { foo, \"bar\": (new baz:qux {...}), \"baz\": foo[\"baz\"].qux };",
            "let x = new foo:bar {\n    foo,\n    \"bar\": (new baz:qux { ... }),\n    \"baz\": foo[\"baz\"].qux,\n};",
        )
        .unwrap();
    }
}
