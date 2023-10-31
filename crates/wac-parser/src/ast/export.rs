use super::{
    display, expr::Expr, parse_optional, parse_token, DocComment, Lookahead, Parse, ParseResult,
    Peek,
};
use crate::lexer::{Lexer, Token};
use serde::Serialize;

/// Represents an export statement in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ExportStatement<'a> {
    /// The doc comments for the statement.
    pub docs: Vec<DocComment<'a>>,
    /// The optional `with` string.
    pub with: Option<super::String<'a>>,
    /// The expression to export.
    pub expr: Expr<'a>,
}

impl<'a> Parse<'a> for ExportStatement<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::ExportKeyword)?;
        let expr = Parse::parse(lexer)?;
        let with = parse_optional(lexer, Token::WithKeyword, Parse::parse)?;
        parse_token(lexer, Token::Semicolon)?;
        Ok(Self { docs, expr, with })
    }
}

impl Peek for ExportStatement<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::ExportKeyword)
    }
}

display!(ExportStatement, export_statement);

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::test::roundtrip;

    #[test]
    fn export_statement_roundtrip() {
        roundtrip::<ExportStatement>("export y;", "export y;").unwrap();
        roundtrip::<ExportStatement>(
            "export foo.%with with \"foo\";",
            "export foo.%with with \"foo\";",
        )
        .unwrap();
        roundtrip::<ExportStatement>("export y.x.z;", "export y.x.z;").unwrap();
        roundtrip::<ExportStatement>("export y.x.z with \"baz\";", "export y.x.z with \"baz\";")
            .unwrap();
        roundtrip::<ExportStatement>("export y[\"x\"][\"z\"];", "export y[\"x\"][\"z\"];").unwrap();
        roundtrip::<ExportStatement>(
            "export y[\"x\"][\"z\"]  with    \"x\";",
            "export y[\"x\"][\"z\"] with \"x\";",
        )
        .unwrap();
        roundtrip::<ExportStatement>(
            "export foo[\"bar\"].baz[\"qux\"];",
            "export foo[\"bar\"].baz[\"qux\"];",
        )
        .unwrap();
        roundtrip::<ExportStatement>(
            "export foo[\"bar\"].baz[\"qux\"] with \"qux\";",
            "export foo[\"bar\"].baz[\"qux\"] with \"qux\";",
        )
        .unwrap();

        roundtrip::<ExportStatement>("export (y);", "export (y);").unwrap();

        roundtrip::<ExportStatement>("export new foo:bar {};", "export new foo:bar {};").unwrap();

        roundtrip::<ExportStatement>(
            "export new foo:bar {}  /* foo */ with     \"foo\";",
            "export new foo:bar {} with \"foo\";",
        )
        .unwrap();

        roundtrip::<ExportStatement>(
            "export new foo:bar { foo, \"bar\": (new baz:qux {a, ...}), \"baz\": foo[\"baz\"].qux };",
            "export new foo:bar {\n    foo,\n    \"bar\": (new baz:qux {\n        a,\n        ...\n    }),\n    \"baz\": foo[\"baz\"].qux,\n};",
        )
        .unwrap();
    }
}
