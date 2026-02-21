//! Module for the AST implementation.

use crate::{
    lexer::{self, Lexer, LexerResult, Token},
    resolution::{AstResolver, Resolution, ResolutionResult},
};
use indexmap::IndexMap;
use miette::{Diagnostic, SourceSpan};
use serde::Serialize;
use std::fmt;
use wac_graph::types::BorrowedPackageKey;

mod export;
mod expr;
mod import;
mod r#let;
mod printer;
mod r#type;

pub use export::*;
pub use expr::*;
pub use import::*;
pub use printer::*;
pub use r#let::*;
pub use r#type::*;

struct Found(Option<Token>);

impl fmt::Display for Found {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Some(t) => t.fmt(f),
            None => write!(f, "end of input"),
        }
    }
}

struct Expected<'a> {
    expected: &'a [Option<Token>],
    count: usize,
}

impl fmt::Display for Expected<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut expected = self.expected.iter().enumerate();
        while let Some((i, Some(token))) = expected.next() {
            if i > 0 {
                write!(f, ", ")?;
            }

            if i == self.count - 1 {
                write!(f, "or ")?;
            }

            token.fmt(f)?;
        }

        if self.count > self.expected.len() {
            write!(f, ", or more...")?;
        }

        Ok(())
    }
}

/// Represents a parse error.
#[derive(thiserror::Error, Diagnostic, Debug)]
#[diagnostic(code("failed to parse document"))]
pub enum Error {
    /// A lexer error occurred.
    #[error("{error}")]
    Lexer {
        /// The lexer error that occurred.
        error: crate::lexer::Error,
        /// The span where the error occurred.
        #[label(primary)]
        span: SourceSpan,
    },
    /// An unexpected token was encountered when a single token was expected.
    #[error("expected {expected}, found {found}", found = Found(*.found))]
    Expected {
        /// The expected token.
        expected: Token,
        /// The found token (`None` for end of input).
        found: Option<Token>,
        /// The span of the found token.
        #[label(primary, "unexpected {found}", found = Found(*.found))]
        span: SourceSpan,
    },
    /// An unexpected token was encountered when either one of two tokens was expected.
    #[error("expected {first} or {second}, found {found}", found = Found(*.found))]
    ExpectedEither {
        /// The first expected token.
        first: Token,
        /// The second expected token.
        second: Token,
        /// The found token.
        found: Option<Token>,
        /// The span of the found token.
        #[label(primary, "unexpected {found}", found = Found(*.found))]
        span: SourceSpan,
    },
    /// An unexpected token was encountered when multiple tokens were expected.
    #[error("expected either {expected}, found {found}", expected = Expected { expected, count: *.count }, found = Found(*.found))]
    ExpectedMultiple {
        /// The tokens that were expected.
        expected: [Option<Token>; 10],
        /// The count of expected tokens.
        count: usize,
        /// The found token.
        found: Option<Token>,
        /// The span of the found token.
        #[label(primary, "unexpected {found}", found = Found(*.found))]
        span: SourceSpan,
    },
    /// An empty type was encountered.
    #[error("{ty} must contain at least one {kind}")]
    EmptyType {
        /// The type that was empty (e.g. "record", "variant", etc.)
        ty: &'static str,
        /// The kind of item that was empty (e.g. "field", "case", etc.)
        kind: &'static str,
        /// The span of the empty type.
        #[label(primary, "empty {ty}")]
        span: SourceSpan,
    },
    /// An invalid semantic version was encountered.
    #[error("`{version}` is not a valid semantic version")]
    InvalidVersion {
        /// The invalid version.
        version: std::string::String,
        /// The span of the version.
        #[label(primary, "invalid version")]
        span: SourceSpan,
    },
}

/// Represents a parse result.
pub type ParseResult<T> = Result<T, Error>;

impl From<(lexer::Error, SourceSpan)> for Error {
    fn from((e, s): (lexer::Error, SourceSpan)) -> Self {
        Self::Lexer { error: e, span: s }
    }
}

/// Expects a given token from the lexer.
pub fn parse_token(lexer: &mut Lexer, expected: Token) -> ParseResult<SourceSpan> {
    let (result, span) = lexer.next().ok_or_else(|| Error::Expected {
        expected,
        found: None,
        span: lexer.span(),
    })?;

    match result {
        Ok(found) if found == expected => Ok(span),
        Ok(found) => Err(Error::Expected {
            expected,
            found: Some(found),
            span,
        }),
        Err(e) => Err((e, span).into()),
    }
}

/// Parses an optional tokens from a lexer.
///
/// The expected token is removed from the token stream before the callback is invoked.
pub fn parse_optional<'a, F, R>(
    lexer: &mut Lexer<'a>,
    expected: Token,
    cb: F,
) -> ParseResult<Option<R>>
where
    F: FnOnce(&mut Lexer<'a>) -> ParseResult<R>,
{
    match lexer.peek() {
        Some((Ok(token), _)) => {
            if token == expected {
                lexer.next();
                Ok(Some(cb(lexer)?))
            } else {
                Ok(None)
            }
        }
        Some((Err(e), s)) => Err((e, s).into()),
        None => Ok(None),
    }
}

/// Used to look ahead one token in the lexer.
///
/// The lookahead stores up to 10 attempted tokens.
pub struct Lookahead {
    next: Option<(LexerResult<Token>, SourceSpan)>,
    attempts: [Option<Token>; 10],
    span: SourceSpan,
    count: usize,
}

impl Lookahead {
    /// Creates a new lookahead from the given lexer.
    pub fn new(lexer: &Lexer) -> Self {
        Self {
            next: lexer.peek(),
            span: lexer.span(),
            attempts: Default::default(),
            count: 0,
        }
    }

    /// Peeks to see if the next token matches the given token.
    pub fn peek(&mut self, expected: Token) -> bool {
        match &self.next {
            Some((Ok(t), _)) if *t == expected => true,
            _ => {
                if self.count < self.attempts.len() {
                    self.attempts[self.count] = Some(expected);
                }

                self.count += 1;
                false
            }
        }
    }

    /// Returns an error based on the attempted tokens.
    ///
    /// Panics if no peeks were attempted.
    pub fn error(self) -> Error {
        let (found, span) = match self.next {
            Some((Ok(token), span)) => (Some(token), span),
            Some((Err(e), s)) => return (e, s).into(),
            None => (None, self.span),
        };

        match self.count {
            0 => unreachable!("lookahead had no attempts"),
            1 => Error::Expected {
                expected: self.attempts[0].unwrap(),
                found,
                span,
            },
            2 => Error::ExpectedEither {
                first: self.attempts[0].unwrap(),
                second: self.attempts[1].unwrap(),
                found,
                span,
            },
            _ => Error::ExpectedMultiple {
                expected: self.attempts,
                count: self.count,
                found,
                span,
            },
        }
    }
}

pub(crate) trait Parse<'a>: Sized {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self>;
}

trait Peek {
    fn peek(lookahead: &mut Lookahead) -> bool;
}

fn parse_delimited<'a, T: Parse<'a> + Peek>(
    lexer: &mut Lexer<'a>,
    until: Token,
    with_commas: bool,
) -> ParseResult<Vec<T>> {
    let mut items = Vec::new();
    loop {
        let mut lookahead = Lookahead::new(lexer);
        if lookahead.peek(until) {
            break;
        }

        if !T::peek(&mut lookahead) {
            return Err(lookahead.error());
        }

        items.push(Parse::parse(lexer)?);

        if let Some((Ok(next), _)) = lexer.peek() {
            if next == until {
                break;
            }

            if with_commas {
                parse_token(lexer, Token::Comma)?;
            }
        }
    }

    Ok(items)
}

/// Represents a package directive in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct PackageDirective<'a> {
    /// The name of the package named by the directive.
    pub package: PackageName<'a>,
    /// The optional world being targeted by the package.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub targets: Option<PackagePath<'a>>,
}

impl<'a> Parse<'a> for PackageDirective<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        parse_token(lexer, Token::PackageKeyword)?;
        let package = Parse::parse(lexer)?;
        let targets = parse_optional(lexer, Token::TargetsKeyword, Parse::parse)?;
        parse_token(lexer, Token::Semicolon)?;
        Ok(Self { package, targets })
    }
}

/// Represents a top-level WAC document.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Document<'a> {
    /// The doc comments for the package.
    pub docs: Vec<DocComment<'a>>,
    /// The package directive of the document.
    pub directive: PackageDirective<'a>,
    /// The statements in the document.
    pub statements: Vec<Statement<'a>>,
}

impl<'a> Document<'a> {
    /// Parses the given source string as a document.
    ///
    /// The given path is used for error reporting.
    pub fn parse(source: &'a str) -> ParseResult<Self> {
        let mut lexer = Lexer::new(source).map_err(Error::from)?;

        let docs = Parse::parse(&mut lexer)?;
        let directive = Parse::parse(&mut lexer)?;

        let mut statements: Vec<Statement> = Default::default();
        while lexer.peek().is_some() {
            statements.push(Parse::parse(&mut lexer)?);
        }

        assert!(lexer.next().is_none(), "expected all tokens to be consumed");
        Ok(Self {
            docs,
            directive,
            statements,
        })
    }

    /// Resolves the document.
    ///
    /// The returned resolution contains an encodable composition graph.
    pub fn resolve(
        &self,
        packages: IndexMap<BorrowedPackageKey<'a>, Vec<u8>>,
    ) -> ResolutionResult<Resolution<'_>> {
        AstResolver::new(self).resolve(packages)
    }
}

/// Represents a statement in the AST.
#[derive(Debug, Clone, Serialize)]
pub enum Statement<'a> {
    /// An import statement.
    Import(ImportStatement<'a>),
    /// A type statement.
    Type(TypeStatement<'a>),
    /// A let statement.
    Let(LetStatement<'a>),
    /// An export statement.
    Export(ExportStatement<'a>),
}

impl<'a> Parse<'a> for Statement<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        let mut lookahead = Lookahead::new(lexer);
        if ImportStatement::peek(&mut lookahead) {
            Ok(Self::Import(Parse::parse(lexer)?))
        } else if LetStatement::peek(&mut lookahead) {
            Ok(Self::Let(Parse::parse(lexer)?))
        } else if ExportStatement::peek(&mut lookahead) {
            Ok(Self::Export(Parse::parse(lexer)?))
        } else if TypeStatement::peek(&mut lookahead) {
            Ok(Self::Type(Parse::parse(lexer)?))
        } else {
            Err(lookahead.error())
        }
    }
}

/// Represents an identifier in the AST.
#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Ident<'a> {
    /// The identifier string.
    pub string: &'a str,
    /// The span of the identifier.
    pub span: SourceSpan,
}

impl<'a> Parse<'a> for Ident<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        let span = parse_token(lexer, Token::Ident)?;
        let id = lexer.source(span);
        Ok(Self {
            string: id.strip_prefix('%').unwrap_or(id),
            span,
        })
    }
}

impl Peek for Ident<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::Ident)
    }
}

/// Represents a string in the AST.
#[derive(Debug, Copy, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct String<'a> {
    /// The value of the string (without quotes).
    pub value: &'a str,
    /// The span of the string.
    pub span: SourceSpan,
}

impl<'a> Parse<'a> for String<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        let span = parse_token(lexer, Token::String)?;
        let s = lexer.source(span);
        Ok(Self {
            value: s.strip_prefix('"').unwrap().strip_suffix('"').unwrap(),
            span,
        })
    }
}

impl Peek for String<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::String)
    }
}

/// Represents a documentation comment in the AST.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DocComment<'a> {
    /// The comment string.
    pub comment: &'a str,
    /// The span of the comment.
    pub span: SourceSpan,
}

impl<'a> Parse<'a> for Vec<DocComment<'a>> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Vec<DocComment<'a>>> {
        Ok(lexer
            .comments()
            .map_err(Error::from)?
            .into_iter()
            .map(|(comment, span)| DocComment { comment, span })
            .collect())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use pretty_assertions::assert_eq;

    /// A test function for parsing a string into an AST node,
    /// converting the AST node into a string, and then comparing
    /// the result with the given expected string.
    ///
    /// Note that we don't expect the input string to be the same
    /// as the output string, since the input string may contain
    /// extra whitespace and comments that are not preserved in
    /// the AST.
    pub(crate) fn roundtrip(source: &str, expected: &str) -> ParseResult<()> {
        let doc = Document::parse(source)?;
        let mut s = std::string::String::new();
        DocumentPrinter::new(&mut s, source, None)
            .document(&doc)
            .unwrap();
        assert_eq!(s, expected, "unexpected AST output");
        Ok(())
    }

    #[test]
    fn document_roundtrip() {
        roundtrip(
            r#"/* ignore me */
/// Doc comment for the package!
package test:foo:bar@1.0.0;
/// Doc comment #1!
import foo: foo:bar/baz;
/// Doc comment #2!
type a = u32;
/// Doc comment #3!
record r {
    x: string
}
/// Doc comment #4!
interface i {
    /// Doc comment #5!
    f: func() -> r;
}
/// Doc comment #6!
world w {
    /// Doc comment #7!
    import i;
    /// Doc comment #8!
    export f: func() -> a;
}
/// Doc comment #9!
let x = new foo:bar { };
/// Doc comment #10!
export x as "foo";
"#,
            r#"/// Doc comment for the package!
package test:foo:bar@1.0.0;

/// Doc comment #1!
import foo: foo:bar/baz;

/// Doc comment #2!
type a = u32;

/// Doc comment #3!
record r {
    x: string,
}

/// Doc comment #4!
interface i {
    /// Doc comment #5!
    f: func() -> r;
}

/// Doc comment #6!
world w {
    /// Doc comment #7!
    import i;

    /// Doc comment #8!
    export f: func() -> a;
}

/// Doc comment #9!
let x = new foo:bar {};

/// Doc comment #10!
export x as "foo";
"#,
        )
        .unwrap()
    }
}
