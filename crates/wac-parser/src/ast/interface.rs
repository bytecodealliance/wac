use super::{
    display,
    keywords::{Interface, Use},
    symbols::{CloseBrace, Colon, Dot, OpenBrace, Semicolon},
    AstDisplay, DocComment, FuncTypeRef, Ident, Indenter, PackagePath, TypeStatement,
};
use crate::parser::Rule;
use pest_ast::FromPest;
use std::fmt;

/// Represents an interface statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::InterfaceStatement))]
pub struct InterfaceStatement<'a> {
    /// The `interface` keyword.
    pub keyword: Interface<'a>,
    /// The identifier of the interface.
    pub id: Ident<'a>,
    /// The body of the interface.
    pub body: InterfaceBody<'a>,
}

impl AstDisplay for InterfaceStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{indenter}{keyword} ", keyword = self.keyword)?;
        self.id.fmt(f, indenter)?;
        self.body.fmt(f, indenter)
    }
}

display!(InterfaceStatement);

/// Represents an interface body in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::InterfaceBody))]
pub struct InterfaceBody<'a> {
    /// The opening brace of the interface body.
    pub open: OpenBrace<'a>,
    /// The items of the interface body.
    pub items: Vec<InterfaceItem<'a>>,
    /// The closing brace of the interface body.
    pub close: CloseBrace<'a>,
}

impl AstDisplay for InterfaceBody<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        writeln!(f, " {open}", open = self.open)?;
        indenter.indent();

        for (i, item) in self.items.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }

            item.fmt(f, indenter)?;
            writeln!(f)?;
        }

        indenter.dedent();
        write!(f, "{indenter}{close}", close = self.close)
    }
}

display!(InterfaceBody);

/// Represents an interface item in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::InterfaceItem))]
pub struct InterfaceItem<'a> {
    /// The doc comments for the interface item.
    pub docs: Vec<DocComment<'a>>,
    /// The interface item kind.
    pub kind: InterfaceItemKind<'a>,
}

impl AstDisplay for InterfaceItem<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        for doc in &self.docs {
            doc.fmt(f, indenter)?;
        }

        self.kind.fmt(f, indenter)
    }
}

display!(InterfaceItem);

/// Represents an interface item kind in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::InterfaceItemKind))]
pub enum InterfaceItemKind<'a> {
    /// The item is a use statement.
    Use(Box<UseStatement<'a>>),
    /// The item is a type statement.
    Type(TypeStatement<'a>),
    /// The item is an interface export statement.
    Export(InterfaceExportStatement<'a>),
}

impl AstDisplay for InterfaceItemKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Use(u) => u.fmt(f, indenter),
            Self::Type(ty) => ty.fmt(f, indenter),
            Self::Export(e) => e.fmt(f, indenter),
        }
    }
}

display!(InterfaceItemKind);

/// Represents a use statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::UseStatement))]
pub struct UseStatement<'a> {
    /// The use keyword in the statement.
    pub keyword: Use<'a>,
    /// The items being used.
    pub items: UseItems<'a>,
    /// The semicolon of the export statement.
    pub semicolon: Semicolon<'a>,
}

impl AstDisplay for UseStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{indenter}{keyword} ", keyword = self.keyword)?;
        self.items.fmt(f, indenter)?;
        write!(f, "{semi}", semi = self.semicolon)
    }
}

display!(UseStatement);

/// Represents the items being used in a use statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::UseItems))]
pub struct UseItems<'a> {
    /// The path to the interface or world being used.
    pub path: UsePath<'a>,
    /// The dot in the statement.
    pub dot: Dot<'a>,
    /// The opening brace of the statement.
    pub open: OpenBrace<'a>,
    /// The items being used.
    pub items: Vec<Ident<'a>>,
    /// The closing brace of the use items.
    pub close: CloseBrace<'a>,
}

impl AstDisplay for UseItems<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        self.path.fmt(f, indenter)?;
        write!(f, "{dot}{open} ", dot = self.dot, open = self.open)?;

        for (i, item) in self.items.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            item.fmt(f, indenter)?;
        }

        write!(f, " {close}", close = self.close)
    }
}

display!(UseItems);

/// Represents a use path in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::UsePath))]
pub enum UsePath<'a> {
    /// The path is a package path.
    Package(PackagePath<'a>),
    /// The path is an identifier.
    Ident(Ident<'a>),
}

impl AstDisplay for UsePath<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Package(pkg) => pkg.fmt(f, indenter),
            Self::Ident(id) => id.fmt(f, indenter),
        }
    }
}

display!(UsePath);

/// Represents an interface export statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::InterfaceExportStatement))]
pub struct InterfaceExportStatement<'a> {
    /// The identifier of the export.
    pub id: Ident<'a>,
    /// The colon of the export statement.
    pub colon: Colon<'a>,
    /// The type of the export.
    pub ty: FuncTypeRef<'a>,
    /// The semicolon of the export statement.
    pub semicolon: Semicolon<'a>,
}

impl AstDisplay for InterfaceExportStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{indenter}")?;
        self.id.fmt(f, indenter)?;
        write!(f, "{colon} ", colon = self.colon)?;
        self.ty.fmt(f, indenter)?;
        write!(f, "{semi}", semi = self.semicolon)
    }
}

display!(InterfaceExportStatement);

#[cfg(test)]
mod test {
    use super::*;
    use crate::{ast::test::roundtrip, parser::Rule};

    #[test]
    fn interface_roundtrip() {
        roundtrip::<InterfaceStatement>(
            Rule::InterfaceStatement,
            r#"interface foo {
            /// Type t
            type t = list<string>;

            use foo.{ x, y, };

            /// Function a
            a: func(a: string, b: string) -> string;

            // not a doc comment
            type x = func() -> list<string>;
            
            /// Function b
            b: x;
}
            "#,
            r#"interface foo {
  /// Type t
  type t = list<string>;

  use foo.{ x, y };

  /// Function a
  a: func(a: string, b: string) -> string;

  type x = func() -> list<string>;

  /// Function b
  b: x;
}"#,
        )
        .unwrap();
    }
}
