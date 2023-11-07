use super::{
    display, parse_optional, parse_token, DocComment, FuncType, Ident, InlineInterface, Lookahead,
    Parse, ParseResult, Peek,
};
use crate::lexer::{Lexer, Span, Token};
use serde::Serialize;

/// Represents an import statement in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ImportStatement<'a> {
    /// The doc comments for the statement.
    pub docs: Vec<DocComment<'a>>,
    /// The identifier of the imported item.
    pub id: Ident<'a>,
    /// The optional `with` string.
    pub with: Option<super::String<'a>>,
    /// The type of the imported item.
    pub ty: ImportType<'a>,
}

impl<'a> Parse<'a> for ImportStatement<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let docs = Parse::parse(lexer)?;
        parse_token(lexer, Token::ImportKeyword)?;
        let id = Parse::parse(lexer)?;
        let with = parse_optional(lexer, Token::WithKeyword, Parse::parse)?;
        parse_token(lexer, Token::Colon)?;
        let ty = Parse::parse(lexer)?;
        parse_token(lexer, Token::Semicolon)?;
        Ok(Self { docs, id, with, ty })
    }
}

impl Peek for ImportStatement<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::ImportKeyword)
    }
}

display!(ImportStatement, import_statement);

/// Represents an import type in the AST.
#[derive(Debug, Clone, Serialize)]
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

impl<'a> Parse<'a> for ImportType<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let mut lookahead = Lookahead::new(lexer);
        if FuncType::peek(&mut lookahead) {
            Ok(Self::Func(Parse::parse(lexer)?))
        } else if InlineInterface::peek(&mut lookahead) {
            Ok(Self::Interface(Parse::parse(lexer)?))
        } else if PackagePath::peek(&mut lookahead) {
            Ok(Self::Package(Parse::parse(lexer)?))
        } else if Ident::peek(&mut lookahead) {
            Ok(Self::Ident(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

/// Represents a package path in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct PackagePath<'a> {
    /// The span of the package path.
    pub span: Span<'a>,
    /// The name of the package.
    pub name: &'a str,
    /// The path segments.
    pub segments: &'a str,
    /// The optional version of the package.
    pub version: Option<&'a str>,
}

impl<'a> PackagePath<'a> {
    /// Gets the span of only the package name.
    pub fn package_name_span(&self) -> Span<'a> {
        Span::from_span(
            self.span.source(),
            &(self.span.start..self.span.start + self.name.len()),
        )
    }

    /// Iterates over the segments of the package path.
    pub fn segment_spans<'b>(&'b self) -> impl Iterator<Item = (&'a str, Span<'a>)> + 'b {
        self.segments.split('/').map(|s| {
            let start = s.as_ptr() as usize - self.name.as_ptr() as usize;
            let end = start + s.len();
            (s, Span::from_span(self.span.source(), &(start..end)))
        })
    }
}

impl<'a> Parse<'a> for PackagePath<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let span = parse_token(lexer, Token::PackagePath)?;
        let s = span.as_str();
        let slash = s.find('/').unwrap();
        let at = s.find('@');
        let name = &s[..slash];
        let segments = &s[slash + 1..at.unwrap_or(slash + s.len() - name.len())];
        let version = at.map(|at| &s[at + 1..]);

        Ok(Self {
            span,
            name,
            segments,
            version,
        })
    }
}

impl Peek for PackagePath<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::PackagePath)
    }
}

/// Represents a package name in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct PackageName<'a> {
    /// The name of the package.
    pub name: &'a str,
    /// The span of the package name,
    pub span: Span<'a>,
}

impl<'a> Parse<'a> for PackageName<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let span = parse_token(lexer, Token::PackageName)?;
        let name = span.as_str();
        Ok(Self { name, span })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ast::test::roundtrip;

    #[test]
    fn import_via_package_roundtrip() {
        roundtrip::<ImportStatement>(
            "import x: foo:bar:baz/qux/jam@1.2.3-preview+abc;",
            "import x: foo:bar:baz/qux/jam@1.2.3-preview+abc;",
        )
        .unwrap();

        roundtrip::<ImportStatement>(
            "import x with \"y\": foo:bar:baz/qux/jam@1.2.3-preview+abc;",
            "import x with \"y\": foo:bar:baz/qux/jam@1.2.3-preview+abc;",
        )
        .unwrap();
    }

    #[test]
    fn import_function_roundtrip() {
        roundtrip::<ImportStatement>(
            "import x: func(x: string) -> string;",
            "import x: func(x: string) -> string;",
        )
        .unwrap();

        roundtrip::<ImportStatement>(
            "import x with \"foo\": func(x: string) -> string;",
            "import x with \"foo\": func(x: string) -> string;",
        )
        .unwrap();
    }

    #[test]
    fn import_interface_roundtrip() {
        roundtrip::<ImportStatement>(
            "import x: interface { x: func(x: string) -> string; };",
            "import x: interface {\n    x: func(x: string) -> string;\n};",
        )
        .unwrap();

        roundtrip::<ImportStatement>(
            "import x with \"foo\": interface { x: func(x: string) -> string; };",
            "import x with \"foo\": interface {\n    x: func(x: string) -> string;\n};",
        )
        .unwrap();
    }

    #[test]
    fn import_via_ident_roundtrip() {
        roundtrip::<ImportStatement>("import x: y;", "import x: y;").unwrap();

        roundtrip::<ImportStatement>(
            "import x /*foo */ with    \"foo\": y;",
            "import x with \"foo\": y;",
        )
        .unwrap();
    }
}
