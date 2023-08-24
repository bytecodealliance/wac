use super::{
    display, keywords::Export, symbols::Semicolon, AstDisplay, Expr, Indenter, WithClause,
};
use crate::parser::Rule;
use pest_ast::FromPest;
use std::fmt;

/// Represents an export statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::ExportStatement))]
pub struct ExportStatement<'a> {
    /// The export keyword in the statement.
    pub keyword: Export<'a>,
    /// The expression to export.
    pub expr: Expr<'a>,
    /// The optional with clause.
    pub with: Option<WithClause<'a>>,
    /// The semicolon in the statement.
    pub semicolon: Semicolon<'a>,
}

impl AstDisplay for ExportStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{indenter}{keyword} ", keyword = self.keyword)?;

        self.expr.fmt(f, indenter)?;

        if let Some(with) = &self.with {
            write!(f, " ")?;
            with.fmt(f, indenter)?;
        }

        write!(f, "{semi}", semi = self.semicolon)
    }
}

display!(ExportStatement);

#[cfg(test)]
mod test {
    use super::*;
    use crate::{ast::test::roundtrip, parser::Rule};

    #[test]
    fn export_statement_roundtrip() {
        roundtrip::<ExportStatement>(Rule::ExportStatement, "export y;", "export y;").unwrap();
        roundtrip::<ExportStatement>(
            Rule::ExportStatement,
            "export foo.%with with \"foo\";",
            "export foo.%with with \"foo\";",
        )
        .unwrap();
        roundtrip::<ExportStatement>(Rule::ExportStatement, "export y.x.z;", "export y.x.z;")
            .unwrap();
        roundtrip::<ExportStatement>(
            Rule::ExportStatement,
            "export y.x.z with \"baz\";",
            "export y.x.z with \"baz\";",
        )
        .unwrap();
        roundtrip::<ExportStatement>(
            Rule::ExportStatement,
            "export y[\"x\"][\"z\"];",
            "export y[\"x\"][\"z\"];",
        )
        .unwrap();
        roundtrip::<ExportStatement>(
            Rule::ExportStatement,
            "export y[\"x\"][\"z\"]  with    \"x\";",
            "export y[\"x\"][\"z\"] with \"x\";",
        )
        .unwrap();
        roundtrip::<ExportStatement>(
            Rule::ExportStatement,
            "export foo[\"bar\"].baz[\"qux\"];",
            "export foo[\"bar\"].baz[\"qux\"];",
        )
        .unwrap();
        roundtrip::<ExportStatement>(
            Rule::ExportStatement,
            "export foo[\"bar\"].baz[\"qux\"] with \"qux\";",
            "export foo[\"bar\"].baz[\"qux\"] with \"qux\";",
        )
        .unwrap();

        roundtrip::<ExportStatement>(Rule::ExportStatement, "export (y);", "export (y);").unwrap();

        roundtrip::<ExportStatement>(
            Rule::ExportStatement,
            "export new foo:bar {};",
            "export new foo:bar {};",
        )
        .unwrap();

        roundtrip::<ExportStatement>(
            Rule::ExportStatement,
            "export new foo:bar {}  /* foo */ with     \"foo\";",
            "export new foo:bar {} with \"foo\";",
        )
        .unwrap();

        roundtrip::<ExportStatement>(
            Rule::ExportStatement,
            "export new foo:bar { foo, bar: (new baz:qux {...}), baz: foo[\"baz\"].qux };",
            "export new foo:bar {\n  foo,\n  bar: (new baz:qux { ... }),\n  baz: foo[\"baz\"].qux,\n};",
        )
        .unwrap();
    }
}
