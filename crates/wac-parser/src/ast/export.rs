use super::{
    expr::Expr, parse_optional, parse_token, DocComment, Lookahead, Parse, ParseResult, Peek,
};
use crate::lexer::{Lexer, Token};
use miette::SourceSpan;
use serde::Serialize;

/// Represents an export statement in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ExportStatement<'a> {
    /// The doc comments for the statement.
    pub docs: Vec<DocComment<'a>>,
    /// The span of the export keyword.
    pub span: SourceSpan,
    /// The optional `with` string.
    pub with: Option<super::String<'a>>,
    /// The expression to export.
    pub expr: Expr<'a>,
}

impl<'a> Parse<'a> for ExportStatement<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        let docs = Parse::parse(lexer)?;
        let span = parse_token(lexer, Token::ExportKeyword)?;
        let expr = Parse::parse(lexer)?;
        let with = parse_optional(lexer, Token::WithKeyword, Parse::parse)?;
        parse_token(lexer, Token::Semicolon)?;
        Ok(Self {
            docs,
            span,
            expr,
            with,
        })
    }
}

impl Peek for ExportStatement<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::ExportKeyword)
    }
}

#[cfg(test)]
mod test {
    use crate::ast::test::roundtrip;

    #[test]
    fn export_statement_roundtrip() {
        roundtrip(
            "package foo:bar; export y;",
            "package foo:bar;\n\nexport y;\n",
        )
        .unwrap();
        roundtrip(
            "package foo:bar; export foo.%with with \"foo\";",
            "package foo:bar;\n\nexport foo.%with with \"foo\";\n",
        )
        .unwrap();
        roundtrip(
            "package foo:bar; export y.x.z;",
            "package foo:bar;\n\nexport y.x.z;\n",
        )
        .unwrap();
        roundtrip(
            "package foo:bar; export y.x.z with \"baz\";",
            "package foo:bar;\n\nexport y.x.z with \"baz\";\n",
        )
        .unwrap();
        roundtrip(
            "package foo:bar; export y[\"x\"][\"z\"];",
            "package foo:bar;\n\nexport y[\"x\"][\"z\"];\n",
        )
        .unwrap();
        roundtrip(
            "package foo:bar; export y[\"x\"][\"z\"]  with    \"x\";",
            "package foo:bar;\n\nexport y[\"x\"][\"z\"] with \"x\";\n",
        )
        .unwrap();
        roundtrip(
            "package foo:bar; export foo[\"bar\"].baz[\"qux\"];",
            "package foo:bar;\n\nexport foo[\"bar\"].baz[\"qux\"];\n",
        )
        .unwrap();
        roundtrip(
            "package foo:bar; export foo[\"bar\"].baz[\"qux\"] with \"qux\";",
            "package foo:bar;\n\nexport foo[\"bar\"].baz[\"qux\"] with \"qux\";\n",
        )
        .unwrap();

        roundtrip(
            "package foo:bar; export (y);",
            "package foo:bar;\n\nexport (y);\n",
        )
        .unwrap();

        roundtrip(
            "package foo:bar; export new foo:bar {};",
            "package foo:bar;\n\nexport new foo:bar {};\n",
        )
        .unwrap();

        roundtrip(
            "package foo:bar; export new foo:bar {}  /* foo */ with     \"foo\";",
            "package foo:bar;\n\nexport new foo:bar {} with \"foo\";\n",
        )
        .unwrap();

        roundtrip(
            "package foo:bar; export new foo:bar { foo, \"bar\": (new baz:qux {a, ...}), \"baz\": foo[\"baz\"].qux };",
            "package foo:bar;\n\nexport new foo:bar {\n    foo,\n    \"bar\": (new baz:qux {\n        a,\n        ...\n    }),\n    \"baz\": foo[\"baz\"].qux,\n};\n",
        )
        .unwrap();
    }
}
