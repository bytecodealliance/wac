//! Module for the AST implementation.

use crate::{
    lexer::{self, Lexer, LexerResult, Span, Token},
    Spanned,
};
use serde::Serialize;
use std::{fmt, path::Path};

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
#[derive(thiserror::Error, Debug)]
pub enum Error<'a> {
    /// A lexer error occurred.
    #[error("{error}")]
    Lexer {
        /// The lexer error that occurred.
        error: crate::lexer::Error,
        /// The span where the error occurred.
        span: Span<'a>,
    },
    /// An unexpected token was encountered when a single token was expected.
    #[error("expected {expected}, found {found}", found = Found(*.found))]
    Expected {
        /// The expected token.
        expected: Token,
        /// The found token (`None` for end of input).
        found: Option<Token>,
        /// The span of the found token.
        span: Span<'a>,
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
        span: Span<'a>,
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
        span: Span<'a>,
    },
    /// An empty type was encountered.
    #[error("{ty} must contain at least one {kind}")]
    EmptyType {
        /// The type that was empty (e.g. "record", "variant", etc.)
        ty: &'static str,
        /// The kind of item that was empty (e.g. "field", "case", etc.)
        kind: &'static str,
        /// The span of the empty type.
        span: Span<'a>,
    },
    /// An invalid semantic version was encountered.
    #[error("`{version}` is not a valid semantic version")]
    InvalidVersion {
        /// The invalid version.
        version: &'a str,
        /// The span of the version.
        span: Span<'a>,
    },
}

impl Spanned for Error<'_> {
    fn span(&self) -> Span<'_> {
        match self {
            Error::Lexer { span, .. }
            | Error::Expected { span, .. }
            | Error::ExpectedEither { span, .. }
            | Error::ExpectedMultiple { span, .. }
            | Error::EmptyType { span, .. }
            | Error::InvalidVersion { span, .. } => *span,
        }
    }
}

/// Represents a parse result.
pub type ParseResult<'a, T> = Result<T, Error<'a>>;

impl<'a> From<(lexer::Error, Span<'a>)> for Error<'a> {
    fn from((e, s): (lexer::Error, Span<'a>)) -> Self {
        Self::Lexer { error: e, span: s }
    }
}

/// Expects a given token from the lexer.
pub fn parse_token<'a>(lexer: &mut Lexer<'a>, expected: Token) -> ParseResult<'a, Span<'a>> {
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
) -> ParseResult<'a, Option<R>>
where
    F: FnOnce(&mut Lexer<'a>) -> ParseResult<'a, R>,
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
pub struct Lookahead<'a> {
    next: Option<(LexerResult<'a, Token>, Span<'a>)>,
    source: &'a str,
    attempts: [Option<Token>; 10],
    count: usize,
}

impl<'a> Lookahead<'a> {
    /// Creates a new lookahead from the given lexer.
    pub fn new(lexer: &Lexer<'a>) -> Self {
        Self {
            next: lexer.peek(),
            source: lexer.source(),
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
    pub fn error(self) -> Error<'a> {
        let (found, span) = match self.next {
            Some((Ok(token), span)) => (Some(token), span),
            Some((Err(e), s)) => return (e, s).into(),
            None => (
                None,
                Span::from_span(self.source, &(self.source.len()..self.source.len())),
            ),
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
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self>;
}

fn parse_delimited<'a, T: Parse<'a> + Peek>(
    lexer: &mut Lexer<'a>,
    until: &[Token],
    with_commas: bool,
) -> ParseResult<'a, Vec<T>> {
    assert!(
        !until.is_empty(),
        "must have at least one token to parse until"
    );

    let mut items = Vec::new();
    loop {
        let mut lookahead = Lookahead::new(lexer);
        if until.iter().any(|t| lookahead.peek(*t)) {
            break;
        }

        if !T::peek(&mut lookahead) {
            return Err(lookahead.error());
        }

        items.push(Parse::parse(lexer)?);

        if with_commas {
            if let Some((Ok(Token::Comma), _)) = lexer.peek() {
                lexer.next();
            }
        }
    }

    Ok(items)
}

trait Peek {
    fn peek(lookahead: &mut Lookahead) -> bool;
}

macro_rules! display {
    ($name:ident, $method:ident) => {
        impl std::fmt::Display for $name<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let mut printer = crate::ast::DocumentPrinter::new(f, None);
                printer.$method(self)
            }
        }
    };
}

pub(crate) use display;

/// Represents a top-level WAC document.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Document<'a> {
    /// The path to the document, used for error reporting.
    #[serde(skip)]
    pub path: &'a Path,
    /// The doc comments for the package.
    pub docs: Vec<DocComment<'a>>,
    /// The package name of the document.
    pub package: PackageName<'a>,
    /// The statements in the document.
    pub statements: Vec<Statement<'a>>,
}

impl<'a> Document<'a> {
    /// Parses the given source string as a document.
    ///
    /// The given path is used for error reporting.
    pub fn parse(source: &'a str, path: &'a Path) -> ParseResult<'a, Self> {
        let mut lexer = Lexer::new(source).map_err(Error::from)?;

        let docs = Parse::parse(&mut lexer)?;

        parse_token(&mut lexer, Token::PackageKeyword)?;
        let package = Parse::parse(&mut lexer)?;
        parse_token(&mut lexer, Token::Semicolon)?;

        let mut statements: Vec<Statement> = Default::default();
        while lexer.peek().is_some() {
            statements.push(Parse::parse(&mut lexer)?);
        }

        assert!(lexer.next().is_none(), "expected all tokens to be consumed");
        Ok(Self {
            path,
            docs,
            package,
            statements,
        })
    }
}

display!(Document, document);

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
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
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
    pub span: Span<'a>,
}

impl<'a> Parse<'a> for Ident<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let span = parse_token(lexer, Token::Ident)?;
        let id = span.as_str();
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
    pub span: Span<'a>,
}

impl<'a> Parse<'a> for String<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Self> {
        let span = parse_token(lexer, Token::String)?;
        let s = span.as_str();
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
    pub span: Span<'a>,
}

impl<'a> Parse<'a> for Vec<DocComment<'a>> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<'a, Vec<DocComment<'a>>> {
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
    pub(crate) fn roundtrip<'a, T: Parse<'a> + fmt::Display>(
        source: &'a str,
        expected: &str,
    ) -> ParseResult<'a, ()> {
        let mut lexer = Lexer::new(source).map_err(Error::from)?;
        let node: T = Parse::parse(&mut lexer)?;
        assert_eq!(node.to_string(), expected, "unexpected AST output");
        Ok(())
    }

    #[test]
    fn document_roundtrip() {
        let document = Document::parse(
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
export x with "foo";
"#,
            Path::new("test"),
        )
        .unwrap();

        assert_eq!(
            document.to_string(),
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
export x with "foo";
"#
        );
    }
}
