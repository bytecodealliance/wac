use super::{
    display,
    keywords::New,
    symbols::{
        CloseBrace, CloseBracket, CloseParen, Colon, Dot, Ellipsis, OpenBrace, OpenBracket,
        OpenParen,
    },
    AstDisplay, Ident, Indenter, PackageName,
};
use crate::parser::Rule;
use pest_ast::FromPest;
use serde::Serialize;
use std::fmt;

/// Represents an expression in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::Expr))]
#[serde(rename_all = "camelCase")]
pub struct Expr<'a> {
    /// The primary expression.
    pub primary: PrimaryExpr<'a>,
    /// The postfix expressions
    pub postfix: Vec<PostfixExpr<'a>>,
}

impl AstDisplay for Expr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        self.primary.fmt(f, indenter)?;

        for postfix in &self.postfix {
            postfix.fmt(f, indenter)?;
        }

        Ok(())
    }
}

display!(Expr);

/// Represents a primary expression in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::PrimaryExpr))]
#[serde(rename_all = "camelCase")]
pub enum PrimaryExpr<'a> {
    /// A new expression.
    New(NewExpr<'a>),
    /// A nested expression.
    Nested(NestedExpr<'a>),
    /// An identifier.
    Ident(Ident<'a>),
}

impl AstDisplay for PrimaryExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            PrimaryExpr::New(new) => new.fmt(f, indenter),
            PrimaryExpr::Nested(nested) => nested.fmt(f, indenter),
            PrimaryExpr::Ident(ident) => ident.fmt(f, indenter),
        }
    }
}

display!(PrimaryExpr);

/// Represents a new expression in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::NewExpr))]
#[serde(rename_all = "camelCase")]
pub struct NewExpr<'a> {
    /// The new keyword in the expression.
    pub keyword: New<'a>,
    /// The package name in the expression.
    pub package_name: PackageName<'a>,
    /// The new expression body.
    pub body: NewExprBody<'a>,
}

impl AstDisplay for NewExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(
            f,
            "{keyword} {package_name} ",
            keyword = self.keyword,
            package_name = self.package_name,
        )?;

        self.body.fmt(f, indenter)
    }
}

display!(NewExpr);

/// Represents a new expression body in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::NewExprBody))]
#[serde(rename_all = "camelCase")]
pub struct NewExprBody<'a> {
    /// The open brace in the expression.
    pub open: OpenBrace<'a>,
    /// The instantiation arguments in the expression.
    pub arguments: Vec<InstantiationArgument<'a>>,
    /// The optional trailing ellipsis in the expression.
    pub ellipsis: Option<Ellipsis<'a>>,
    /// The close brace in the expression.
    pub close: CloseBrace<'a>,
}

impl AstDisplay for NewExprBody<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        if self.arguments.is_empty() {
            match &self.ellipsis {
                Some(ellipsis) => {
                    write!(
                        f,
                        "{open} {ellipsis} {close}",
                        open = self.open,
                        ellipsis = ellipsis,
                        close = self.close
                    )?;
                }
                None => {
                    write!(f, "{open}{close}", open = self.open, close = self.close)?;
                }
            }
            return Ok(());
        }

        writeln!(f, "{open}", open = self.open)?;

        indenter.indent();
        for arg in &self.arguments {
            write!(f, "{indenter}")?;
            arg.fmt(f, indenter)?;
            writeln!(f, ",")?;
        }

        if let Some(ellipsis) = &self.ellipsis {
            write!(f, "{indenter}{ellipsis}")?;
        }

        indenter.dedent();
        write!(f, "{close}", close = self.close)
    }
}

display!(NewExprBody);

/// Represents an instantiation argument in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::InstantiationArgument))]
#[serde(rename_all = "camelCase")]
pub enum InstantiationArgument<'a> {
    /// The argument is a named instantiation argument.
    Named(NamedInstantiationArgument<'a>),
    /// The argument is an identifier.
    Ident(Ident<'a>),
}

impl AstDisplay for InstantiationArgument<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            InstantiationArgument::Named(named) => named.fmt(f, indenter),
            InstantiationArgument::Ident(ident) => ident.fmt(f, indenter),
        }
    }
}

display!(InstantiationArgument);

/// Represents a named instantiation argument in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::NamedInstantiationArgument))]
#[serde(rename_all = "camelCase")]
pub struct NamedInstantiationArgument<'a> {
    /// The identifier in the argument.
    pub id: Ident<'a>,
    /// The colon in the argument.
    pub colon: Colon<'a>,
    /// The expression in the argument.
    pub expr: Expr<'a>,
}

impl AstDisplay for NamedInstantiationArgument<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{id}{colon} ", id = self.id, colon = self.colon)?;
        self.expr.fmt(f, indenter)
    }
}

display!(NamedInstantiationArgument);

/// Represents a nested expression in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::NestedExpr))]
#[serde(rename_all = "camelCase")]
pub struct NestedExpr<'a> {
    /// The open paren in the expression.
    pub open: OpenParen<'a>,
    /// The nested expression.
    pub expr: Box<Expr<'a>>,
    /// The close paren in the expression.
    pub close: CloseParen<'a>,
}

impl AstDisplay for NestedExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{open}", open = self.open)?;
        self.expr.fmt(f, indenter)?;
        write!(f, "{close}", close = self.close)
    }
}

display!(NestedExpr);

/// Represents a postfix expression in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::PostfixExpr))]
#[serde(rename_all = "camelCase")]
pub enum PostfixExpr<'a> {
    /// The postfix expression is an access expression.
    Access(AccessExpr<'a>),
    /// The postfix expression is a named access expression.
    NamedAccess(NamedAccessExpr<'a>),
}

impl AstDisplay for PostfixExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            PostfixExpr::Access(access) => access.fmt(f, indenter),
            PostfixExpr::NamedAccess(named_access) => named_access.fmt(f, indenter),
        }
    }
}

display!(PostfixExpr);

/// Represents an access expression in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::AccessExpr))]
#[serde(rename_all = "camelCase")]
pub struct AccessExpr<'a> {
    /// The dot in the expression.
    pub dot: Dot<'a>,
    /// The identifier in the expression.
    pub id: Ident<'a>,
}

impl AstDisplay for AccessExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, _indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{dot}{id}", dot = self.dot, id = self.id)
    }
}

display!(AccessExpr);

/// Represents a named access expression in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::NamedAccessExpr))]
#[serde(rename_all = "camelCase")]
pub struct NamedAccessExpr<'a> {
    /// The open bracket in the expression.
    pub open: OpenBracket<'a>,
    /// The name string in the expression.
    pub string: super::String<'a>,
    /// The close bracket in the expression.
    pub close: CloseBracket<'a>,
}

impl AstDisplay for NamedAccessExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, _indenter: &mut Indenter) -> fmt::Result {
        write!(
            f,
            "{open}{string}{close}",
            open = self.open,
            string = self.string,
            close = self.close
        )
    }
}

display!(NamedAccessExpr);

#[cfg(test)]
mod test {
    use super::*;
    use crate::{ast::test::roundtrip, parser::Rule};

    #[test]
    fn primary_expr_roundtrip() {
        roundtrip::<Expr>(Rule::Expr, "x", "x").unwrap();
        roundtrip::<Expr>(Rule::Expr, "y.x.z", "y.x.z").unwrap();
        roundtrip::<Expr>(Rule::Expr, "y[\"x\"][\"z\"]", "y[\"x\"][\"z\"]").unwrap();
        roundtrip::<Expr>(
            Rule::Expr,
            "foo[\"bar\"].baz[\"qux\"]",
            "foo[\"bar\"].baz[\"qux\"]",
        )
        .unwrap();

        roundtrip::<Expr>(Rule::Expr, "(foo-bar-baz)", "(foo-bar-baz)").unwrap();

        roundtrip::<Expr>(Rule::Expr, "new foo:bar {}", "new foo:bar {}").unwrap();

        roundtrip::<Expr>(
            Rule::Expr,
            "new foo:bar { foo, bar: (new baz:qux {...}), baz: foo[\"baz\"].qux }",
            "new foo:bar {\n  foo,\n  bar: (new baz:qux { ... }),\n  baz: foo[\"baz\"].qux,\n}",
        )
        .unwrap();
    }
}
