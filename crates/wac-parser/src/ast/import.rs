use super::{
    display,
    keywords::{Import, With},
    serialize_span,
    symbols::{At, Colon, Semicolon, Slash},
    AstDisplay, FuncType, Ident, Indenter, InlineInterface,
};
use crate::parser::Rule;
use anyhow::Result;
use pest::Span;
use pest_ast::FromPest;
use semver::Version;
use serde::Serialize;
use std::fmt;

/// Represents an import statement in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::ImportStatement))]
#[serde(rename_all = "camelCase")]
pub struct ImportStatement<'a> {
    /// The import keyword in the statement.
    pub keyword: Import<'a>,
    /// The identifier of the imported item.
    pub id: Ident<'a>,
    /// The optional with clause.
    pub with: Option<WithClause<'a>>,
    /// The colon in the statement.
    pub colon: Colon<'a>,
    /// The type of the imported item.
    pub ty: ImportType<'a>,
    /// The semicolon in the statement.
    pub semicolon: Semicolon<'a>,
}

impl AstDisplay for ImportStatement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(
            f,
            "{indenter}{keyword} {id}",
            keyword = self.keyword,
            id = self.id
        )?;

        if let Some(with) = &self.with {
            write!(f, " ")?;
            with.fmt(f, indenter)?;
        }

        write!(f, "{colon} ", colon = self.colon)?;
        self.ty.fmt(f, indenter)?;
        write!(f, "{semi}", semi = self.semicolon)
    }
}

display!(ImportStatement);

/// Represents an import type in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::ImportType))]
#[serde(rename_all = "camelCase")]
pub enum ImportType<'a> {
    /// The import type is from a package path.
    Package(PackagePath<'a>),
    /// The import type is a function.
    Func(FuncType<'a>),
    /// The import type is an interface.
    Interface(InlineInterface<'a>),
    /// The import type is an identifier.
    Ident(Ident<'a>),
}

impl AstDisplay for ImportType<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Package(pkg) => pkg.fmt(f, indenter),
            Self::Func(ty) => ty.fmt(f, indenter),
            Self::Interface(ty) => ty.fmt(f, indenter),
            Self::Ident(id) => id.fmt(f, indenter),
        }
    }
}

display!(ImportType);

/// Represents a `with` clause in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::WithClause))]
#[serde(rename_all = "camelCase")]
pub struct WithClause<'a> {
    /// The `with` keyword in the clause.
    pub keyword: With<'a>,
    /// The name to import with.
    pub name: super::String<'a>,
}

impl AstDisplay for WithClause<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{keyword} ", keyword = self.keyword,)?;
        self.name.fmt(f, indenter)
    }
}

display!(WithClause);

/// Represents a package path in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::PackagePath))]
#[serde(rename_all = "camelCase")]
pub struct PackagePath<'a> {
    /// The name of the package.
    pub name: PackageName<'a>,
    /// The path segments.
    pub segments: Vec<(Slash<'a>, Ident<'a>)>,
    /// The optional version of the package.
    pub version: Option<(At<'a>, PackageVersion<'a>)>,
}

impl PackagePath<'_> {
    /// Calculates the span of the package path.
    pub fn span(&self) -> Span {
        let span = self.name.span();
        let end = if let Some((_, version)) = &self.version {
            version.0.end()
        } else {
            self.segments_span().end()
        };

        Span::new(span.get_input(), span.start(), end).unwrap()
    }

    /// Returns the string representation of the package path.
    pub fn as_str(&self) -> &str {
        self.span().as_str()
    }

    /// Gets the span of just the path segments.
    pub fn segments_span(&self) -> Span {
        let (_, first) = self.segments.first().unwrap();
        let (_, last) = self.segments.last().unwrap();
        Span::new(first.0.get_input(), first.0.start(), last.0.end()).unwrap()
    }

    /// Gets the path segments as a string.
    pub fn segments(&self) -> &str {
        self.segments_span().as_str()
    }
}

impl AstDisplay for PackagePath<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        self.name.fmt(f, indenter)?;

        for (slash, segment) in &self.segments {
            write!(f, "{slash}")?;
            segment.fmt(f, indenter)?;
        }

        if let Some((at, version)) = &self.version {
            write!(f, "{at}")?;
            version.fmt(f, indenter)?;
        }

        Ok(())
    }
}

display!(PackagePath);

/// Represents a package name in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::PackageName))]
#[serde(rename_all = "camelCase")]
pub struct PackageName<'a> {
    /// The parts of the package name.
    pub parts: Vec<Ident<'a>>,
}

impl PackageName<'_> {
    /// Gets the span of the package name.
    pub fn span(&self) -> Span {
        let span = self.parts.first().unwrap().0;
        let end = self.parts.last().map(|i| i.0.end()).unwrap();
        Span::new(span.get_input(), span.start(), end).unwrap()
    }

    /// Gets the package name as a string.
    pub fn as_str(&self) -> &str {
        self.span().as_str()
    }
}

impl AstDisplay for PackageName<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        for (i, part) in self.parts.iter().enumerate() {
            if i > 0 {
                write!(f, ":")?;
            }

            part.fmt(f, indenter)?;
        }

        Ok(())
    }
}

display!(PackageName);

/// Represents a package version in the AST.
#[derive(Debug, Clone, Serialize, FromPest)]
#[pest_ast(rule(Rule::PackageVersion))]
#[serde(rename_all = "camelCase")]
pub struct PackageVersion<'a>(
    #[pest_ast(outer())]
    #[serde(serialize_with = "serialize_span")]
    pub Span<'a>,
);

impl PackageVersion<'_> {
    /// Returns the string representation of the package version.
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    /// Returns the package version as a `semver::Version`.
    ///
    /// Returns an error if the package version is not a valid semver version.
    pub fn as_version(&self) -> Result<Version> {
        Ok(Version::parse(self.as_str())?)
    }
}

impl AstDisplay for PackageVersion<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, _indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{version}", version = self.0.as_str())
    }
}

display!(PackageVersion);

#[cfg(test)]
mod test {
    use super::*;
    use crate::{ast::test::roundtrip, parser::Rule};

    #[test]
    fn import_via_package_roundtrip() {
        roundtrip::<ImportStatement>(
            Rule::ImportStatement,
            "import x: foo:bar:baz/qux/jam@1.2.3-preview+abc;",
            "import x: foo:bar:baz/qux/jam@1.2.3-preview+abc;",
        )
        .unwrap();

        roundtrip::<ImportStatement>(
            Rule::ImportStatement,
            "import x with \"y\": foo:bar:baz/qux/jam@1.2.3-preview+abc;",
            "import x with \"y\": foo:bar:baz/qux/jam@1.2.3-preview+abc;",
        )
        .unwrap();
    }

    #[test]
    fn import_function_roundtrip() {
        roundtrip::<ImportStatement>(
            Rule::ImportStatement,
            "import x: func(x: string) -> string;",
            "import x: func(x: string) -> string;",
        )
        .unwrap();

        roundtrip::<ImportStatement>(
            Rule::ImportStatement,
            "import x with \"foo\": func(x: string) -> string;",
            "import x with \"foo\": func(x: string) -> string;",
        )
        .unwrap();
    }

    #[test]
    fn import_interface_roundtrip() {
        roundtrip::<ImportStatement>(
            Rule::ImportStatement,
            "import x: interface { x: func(x: string) -> string; };",
            "import x: interface {\n  x: func(x: string) -> string;\n};",
        )
        .unwrap();

        roundtrip::<ImportStatement>(
            Rule::ImportStatement,
            "import x with \"foo\": interface { x: func(x: string) -> string; };",
            "import x with \"foo\": interface {\n  x: func(x: string) -> string;\n};",
        )
        .unwrap();
    }

    #[test]
    fn import_via_ident_roundtrip() {
        roundtrip::<ImportStatement>(Rule::ImportStatement, "import x: y;", "import x: y;")
            .unwrap();

        roundtrip::<ImportStatement>(
            Rule::ImportStatement,
            "import x /*foo */ with    \"foo\": y;",
            "import x with \"foo\": y;",
        )
        .unwrap();
    }
}
