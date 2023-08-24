use super::{
    display,
    keywords::Let,
    symbols::{Equals, Semicolon},
    AstDisplay, Expr, Ident, Indenter,
};
use crate::parser::Rule;
use pest_ast::FromPest;
use std::fmt;

/// Represents a let statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::LetStatement))]
pub struct LetStatement<'a> {
    /// The let keyword in the statement.
    pub keyword: Let<'a>,
    /// The newly bound identifier.
    pub id: Ident<'a>,
    /// The equals sign in the statement.
    pub equals: Equals<'a>,
    /// The expression being bound.
    pub expr: Expr<'a>,
    /// The semicolon in the statement.
    pub semicolon: Semicolon<'a>,
}

impl AstDisplay for LetStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(
            f,
            "{indenter}{keyword} {id} {equals} ",
            keyword = self.keyword,
            id = self.id,
            equals = self.equals,
        )?;

        self.expr.fmt(f, indenter)?;

        write!(f, "{semi}", semi = self.semicolon)
    }
}

display!(LetStatement);

#[cfg(test)]
mod test {
    use super::*;
    use crate::{ast::test::roundtrip, parser::Rule};

    #[test]
    fn let_statement_roundtrip() {
        roundtrip::<LetStatement>(Rule::LetStatement, "let x= y;", "let x = y;").unwrap();
        roundtrip::<LetStatement>(Rule::LetStatement, "let x =y.x.z;", "let x = y.x.z;").unwrap();
        roundtrip::<LetStatement>(
            Rule::LetStatement,
            "let x=y[\"x\"][\"z\"];",
            "let x = y[\"x\"][\"z\"];",
        )
        .unwrap();
        roundtrip::<LetStatement>(
            Rule::LetStatement,
            "let x = foo[\"bar\"].baz[\"qux\"];",
            "let x = foo[\"bar\"].baz[\"qux\"];",
        )
        .unwrap();

        roundtrip::<LetStatement>(Rule::LetStatement, "let x = (y);", "let x = (y);").unwrap();

        roundtrip::<LetStatement>(
            Rule::LetStatement,
            "let x = new foo:bar {};",
            "let x = new foo:bar {};",
        )
        .unwrap();

        roundtrip::<LetStatement>(
            Rule::LetStatement,
            "let x = new foo:bar { foo, bar: (new baz:qux {...}), baz: foo[\"baz\"].qux };",
            "let x = new foo:bar {\n  foo,\n  bar: (new baz:qux { ... }),\n  baz: foo[\"baz\"].qux,\n};",
        )
        .unwrap();
    }
}
