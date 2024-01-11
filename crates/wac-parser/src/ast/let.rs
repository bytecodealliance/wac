use super::{parse_token, DocComment, Expr, Ident, Lookahead, Parse, ParseResult, Peek};
use crate::lexer::{Lexer, Token};
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
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
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

#[cfg(test)]
mod test {
    use crate::ast::test::roundtrip;

    #[test]
    fn let_statement_roundtrip() {
        roundtrip(
            "package foo:bar; let x= y;",
            "package foo:bar;\n\nlet x = y;\n",
        )
        .unwrap();
        roundtrip(
            "package foo:bar; let x =y.x.z;",
            "package foo:bar;\n\nlet x = y.x.z;\n",
        )
        .unwrap();
        roundtrip(
            "package foo:bar; let x=y[\"x\"][\"z\"];",
            "package foo:bar;\n\nlet x = y[\"x\"][\"z\"];\n",
        )
        .unwrap();
        roundtrip(
            "package foo:bar; let x = foo[\"bar\"].baz[\"qux\"];",
            "package foo:bar;\n\nlet x = foo[\"bar\"].baz[\"qux\"];\n",
        )
        .unwrap();

        roundtrip(
            "package foo:bar; let x = (y);",
            "package foo:bar;\n\nlet x = (y);\n",
        )
        .unwrap();

        roundtrip(
            "package foo:bar; let x = new foo:bar {};",
            "package foo:bar;\n\nlet x = new foo:bar {};\n",
        )
        .unwrap();

        roundtrip(
            "package foo:bar; let x = new foo:bar { foo, \"bar\": (new baz:qux {...}), \"baz\": foo[\"baz\"].qux };",
            "package foo:bar;\n\nlet x = new foo:bar {\n    foo,\n    \"bar\": (new baz:qux { ... }),\n    \"baz\": foo[\"baz\"].qux,\n};\n",
        )
        .unwrap();

        roundtrip(
            "package foo:bar; let x = new foo:bar { foo, ...i, bar: baz, ...i2, ...,};",
            "package foo:bar;\n\nlet x = new foo:bar {\n    foo,\n    ...i,\n    bar: baz,\n    ...i2,\n    ...\n};\n",
        )
        .unwrap();
    }
}
