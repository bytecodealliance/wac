use super::{
    display,
    keywords::{Export, Import, Interface, World},
    symbols::{CloseBrace, Colon, OpenBrace, Semicolon},
    AstDisplay, DocComment, FuncType, Ident, Indenter, InterfaceBody, PackagePath, TypeStatement,
    UseStatement,
};
use crate::parser::Rule;
use pest_ast::FromPest;
use std::fmt;

/// Represents a world statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldStatement))]
pub struct WorldStatement<'a> {
    /// The `world` keyword.
    pub keyword: World<'a>,
    /// The identifier of the world.
    pub id: Ident<'a>,
    /// The body of the world.
    pub body: WorldBody<'a>,
}

impl AstDisplay for WorldStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{indenter}{keyword} ", keyword = self.keyword)?;
        self.id.fmt(f, indenter)?;
        self.body.fmt(f, indenter)
    }
}

display!(WorldStatement);

/// Represents a world body in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldBody))]
pub struct WorldBody<'a> {
    /// The opening brace of the world body.
    pub open: OpenBrace<'a>,
    /// The items of the world body.
    pub items: Vec<WorldItem<'a>>,
    /// The closing brace of the world body.
    pub close: CloseBrace<'a>,
}

impl AstDisplay for WorldBody<'_> {
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

display!(WorldBody);

/// Represents a world item in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldItem))]
pub struct WorldItem<'a> {
    /// The doc comments for the world item.
    pub docs: Vec<DocComment<'a>>,
    /// The world item kind.
    pub kind: WorldItemKind<'a>,
}

impl AstDisplay for WorldItem<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        for doc in &self.docs {
            doc.fmt(f, indenter)?;
        }

        self.kind.fmt(f, indenter)
    }
}

display!(WorldItem);

/// Represents a world item kind in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldItemKind))]
pub enum WorldItemKind<'a> {
    /// The item is a use statement.
    Use(Box<UseStatement<'a>>),
    /// The item is a type statement.
    Type(TypeStatement<'a>),
    /// The item is a world export statement.
    Import(WorldImportStatement<'a>),
    /// The item is a world export statement.
    Export(WorldExportStatement<'a>),
}

impl AstDisplay for WorldItemKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Use(u) => u.fmt(f, indenter),
            Self::Type(ty) => ty.fmt(f, indenter),
            Self::Import(i) => i.fmt(f, indenter),
            Self::Export(e) => e.fmt(f, indenter),
        }
    }
}

display!(WorldItemKind);

/// Represents a world import statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldImportStatement))]
pub struct WorldImportStatement<'a> {
    /// The `import` keyword in the statement.
    pub keyword: Import<'a>,
    /// The declaration of the imported item.
    pub decl: WorldItemDecl<'a>,
    /// The semicolon of the import statement.
    pub semicolon: Semicolon<'a>,
}

impl AstDisplay for WorldImportStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{indenter}{keyword} ", keyword = self.keyword)?;
        self.decl.fmt(f, indenter)?;
        write!(f, "{semi}", semi = self.semicolon)
    }
}

display!(WorldImportStatement);

/// Represents a world export statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldExportStatement))]
pub struct WorldExportStatement<'a> {
    /// The `export` keyword in the statement.
    pub keyword: Export<'a>,
    /// The declaration of the exported item.
    pub decl: WorldItemDecl<'a>,
    /// The semicolon of the export statement.
    pub semicolon: Semicolon<'a>,
}

impl AstDisplay for WorldExportStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{indenter}{keyword} ", keyword = self.keyword)?;
        self.decl.fmt(f, indenter)?;
        write!(f, "{semi}", semi = self.semicolon)
    }
}

display!(WorldExportStatement);

/// Represents a world item declaration in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldItemDecl))]
pub enum WorldItemDecl<'a> {
    /// The declaration is by name.
    Named(WorldNamedItem<'a>),
    /// The declaration is by a reference to an interface.
    Interface(InterfaceRef<'a>),
}

impl AstDisplay for WorldItemDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Named(n) => n.fmt(f, indenter),
            Self::Interface(i) => i.fmt(f, indenter),
        }
    }
}

display!(WorldItemDecl);

/// Represents a world named item in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::WorldNamedItem))]
pub struct WorldNamedItem<'a> {
    /// The identifier of the item being imported or exported.
    pub id: Ident<'a>,
    /// The colon between the identifier and the extern type.
    pub colon: Colon<'a>,
    /// The extern type of the item.
    pub ty: ExternType<'a>,
}

impl AstDisplay for WorldNamedItem<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        self.id.fmt(f, indenter)?;
        write!(f, "{colon} ", colon = self.colon)?;
        self.ty.fmt(f, indenter)
    }
}

display!(WorldNamedItem);

/// Represents a reference to an interface in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::InterfaceRef))]
pub enum InterfaceRef<'a> {
    /// The reference is by identifier.
    Ident(Ident<'a>),
    /// The reference is by package path.
    Path(PackagePath<'a>),
}

impl AstDisplay for InterfaceRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Ident(id) => id.fmt(f, indenter),
            Self::Path(path) => path.fmt(f, indenter),
        }
    }
}

display!(InterfaceRef);

/// Represents the external type of a world item in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::ExternType))]
pub enum ExternType<'a> {
    /// The type is by identifier.
    Ident(Ident<'a>),
    /// The type is an inline function type.
    Func(FuncType<'a>),
    /// The type is an inline interface.
    Interface(InlineInterface<'a>),
}

impl AstDisplay for ExternType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Ident(id) => id.fmt(f, indenter),
            Self::Func(func) => func.fmt(f, indenter),
            Self::Interface(interface) => interface.fmt(f, indenter),
        }
    }
}

display!(ExternType);

/// Represents an inline interface in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::InlineInterface))]
pub struct InlineInterface<'a> {
    /// The `interface` keyword in the inline interface.
    pub keyword: Interface<'a>,
    /// The body of the interface.
    pub body: InterfaceBody<'a>,
}

impl AstDisplay for InlineInterface<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{keyword}", keyword = self.keyword)?;
        self.body.fmt(f, indenter)
    }
}

display!(InlineInterface);

#[cfg(test)]
mod test {
    use super::*;
    use crate::{ast::test::roundtrip, parser::Rule};

    #[test]
    fn interface_roundtrip() {
        roundtrip::<WorldStatement>(
            Rule::WorldStatement,
            r#"world foo {
            /// Type t
            type t = list<string>;

            // not a doc comment
            type x = func() -> list<string>;

            use foo.{ y, };

            /// Import with function type.
            import a: func(a: string, b: string) -> string;

            /// Import with identifier.
            import b: x;

            /// Import with inline interface.
            import c: interface {
                /// Function a
                a: func(a: string, b: string) -> string;
            };

            /// Import with package path
            import foo:bar/baz@1.0.0;

            /// Export with function type.
            export a: func(a: string, b: string) -> string;

            /// Export with identifier.
            export b: x;

            /// Export with inline interface.
            export c: interface {
                /// Function a
                a: func(a: string, b: string) -> string;
            };

            /// Export with package path
            export foo:bar/baz@1.0.0;
}
            "#,
            r#"world foo {
  /// Type t
  type t = list<string>;

  type x = func() -> list<string>;

  use foo.{ y };

  /// Import with function type.
  import a: func(a: string, b: string) -> string;

  /// Import with identifier.
  import b: x;

  /// Import with inline interface.
  import c: interface {
    /// Function a
    a: func(a: string, b: string) -> string;
  };

  /// Import with package path
  import foo:bar/baz@1.0.0;

  /// Export with function type.
  export a: func(a: string, b: string) -> string;

  /// Export with identifier.
  export b: x;

  /// Export with inline interface.
  export c: interface {
    /// Function a
    a: func(a: string, b: string) -> string;
  };

  /// Export with package path
  export foo:bar/baz@1.0.0;
}"#,
        )
        .unwrap();
    }
}
