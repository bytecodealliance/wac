use super::{parse_token, DocComment, Expr, Ident, Lookahead, Parse, ParseResult, Peek, Transform};
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
    /// The right-hand-side of the let..
    pub rhs: LetStatementRhs<'a>,
}

impl<'a> Parse<'a> for LetStatement<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::LetKeyword)?;
        let id = Parse::parse(lexer)?;
        parse_token(lexer, Token::Equals)?;
        let mut lookahead = Lookahead::new(lexer);
        let rhs = if Transform::peek(&mut lookahead) {
            LetStatementRhs::Transform(Parse::parse(lexer)?)
        } else if Expr::peek(&mut lookahead) {
            LetStatementRhs::Expr(Parse::parse(lexer)?)
        } else {
            return Err(lookahead.error());
        };
        parse_token(lexer, Token::Semicolon)?;
        Ok(Self { docs, id, rhs })
    }
}

impl Peek for LetStatement<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::LetKeyword)
    }
}

/// Represents the right-hand-side of a let statement.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum LetStatementRhs<'a> {
    /// The right-hand-side is an expression.
    Expr(Expr<'a>),
    /// The right-hand-side is a transform.
    Transform(Transform<'a>),
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
