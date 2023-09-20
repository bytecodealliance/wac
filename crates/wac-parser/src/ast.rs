//! Module for the AST implementation.

// TODO: remove on next pest-ast release
// see: https://github.com/pest-parser/ast/pull/27
#![allow(clippy::clone_on_copy)]

use crate::parser::{DocumentParser, Rule};
use anyhow::{anyhow, bail, Context};
use from_pest::FromPest as _;
use pest::{
    error::{Error, ErrorVariant},
    Parser, Span,
};
use pest_ast::FromPest;
use std::{fmt, path::Path};

mod export;
mod expr;
mod import;
pub mod keywords;
mod r#let;
pub mod symbols;
mod r#type;

pub use export::*;
pub use expr::*;
pub use import::*;
pub use r#let::*;
pub use r#type::*;

/// Used to indent output when displaying AST nodes.
#[derive(Debug, Clone, Copy, Default)]
pub struct Indenter {
    level: usize,
    repeated: std::option::Option<&'static str>,
}

impl Indenter {
    /// Creates a new indenter.
    ///
    /// The default repeated pattern is two spaces.
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a new indenter with the given repeated pattern per-level.
    pub fn new_with_repeated(repeated: &'static str) -> Self {
        Self {
            level: 0,
            repeated: Some(repeated),
        }
    }

    /// Increases the indentation level.
    pub fn indent(&mut self) {
        self.level = self.level.saturating_add(1);
    }

    /// Decreases the indentation level.
    pub fn dedent(&mut self) {
        self.level = self.level.saturating_sub(1);
    }
}

impl fmt::Display for Indenter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let repeated = self.repeated.unwrap_or("  ");

        for _ in 0..self.level {
            write!(f, "{repeated}")?;
        }

        Ok(())
    }
}

macro_rules! display {
    ($id:ident) => {
        impl std::fmt::Display for $id<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                <Self as AstDisplay>::fmt(self, f, &mut crate::ast::Indenter::new())
            }
        }
    };
}

pub(crate) use display;

/// A trait for displaying AST nodes.
///
/// This differs from `fmt::Display` in that it takes an `Indenter`
/// which can be used to properly indent the output.
pub trait AstDisplay {
    /// Formats the AST node.
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result;
}

/// Creates a new error with the given message and span.
pub fn new_error_with_span(msg: impl fmt::Display, span: Span) -> anyhow::Error {
    anyhow!(Error::new_from_span(
        ErrorVariant::CustomError::<Rule> {
            message: msg.to_string()
        },
        span
    ))
}

#[derive(Debug, Clone, Copy, FromPest)]
#[pest_ast(rule(Rule::EOI))]
struct EndOfInput;

/// Represents the top-level document in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::Document))]
pub struct Document<'a> {
    /// The statements in the document.
    pub statements: Vec<Statement<'a>>,
    _eoi: EndOfInput,
}

impl<'a> Document<'a> {
    /// Parses the given string as a document.
    ///
    /// The given path is the path to display in error messages.
    pub fn parse(contents: &'a str, path: impl AsRef<Path>) -> anyhow::Result<Self> {
        Self::detect_invalid_input(contents)?;

        let path = path.as_ref();

        let mut iter = DocumentParser::parse(Rule::Document, contents)
            .map_err(|mut e| {
                if let Some(path) = path.as_os_str().to_str() {
                    e = e.with_path(path);
                }

                e.renamed_rules(|r| r.rename().to_owned())
            })
            .with_context(|| format!("failed to parse `{path}`", path = path.display()))?;

        Self::from_pest(&mut iter).context("failed to construct AST")
    }

    fn detect_invalid_input(input: &str) -> anyhow::Result<()> {
        // Disallow specific codepoints.
        let mut line = 1;
        for ch in input.chars() {
            match ch {
                '\n' => line += 1,
                '\r' | '\t' => {}

                // Bidirectional override codepoints can be used to craft source code that
                // appears to have a different meaning than its actual meaning. See
                // [CVE-2021-42574] for background and motivation.
                //
                // [CVE-2021-42574]: https://cve.mitre.org/cgi-bin/cvename.cgi?name=CVE-2021-42574
                '\u{202a}' | '\u{202b}' | '\u{202c}' | '\u{202d}' | '\u{202e}' | '\u{2066}'
                | '\u{2067}' | '\u{2068}' | '\u{2069}' => {
                    bail!(
                        "input contains bidirectional override codepoint {:?} at line {line}",
                        ch.escape_unicode(),
                    );
                }

                // Disallow several characters which are deprecated or discouraged in Unicode.
                //
                // U+149 deprecated; see Unicode 13.0.0, sec. 7.1 Latin, Compatibility Digraphs.
                // U+673 deprecated; see Unicode 13.0.0, sec. 9.2 Arabic, Additional Vowel Marks.
                // U+F77 and U+F79 deprecated; see Unicode 13.0.0, sec. 13.4 Tibetan, Vowels.
                // U+17A3 and U+17A4 deprecated, and U+17B4 and U+17B5 discouraged; see
                // Unicode 13.0.0, sec. 16.4 Khmer, Characters Whose Use Is Discouraged.
                '\u{149}' | '\u{673}' | '\u{f77}' | '\u{f79}' | '\u{17a3}' | '\u{17a4}'
                | '\u{17b4}' | '\u{17b5}' => {
                    bail!(
                        "codepoint {:?} at line {line} is discouraged by Unicode",
                        ch.escape_unicode(),
                    );
                }

                // Disallow control codes other than the ones explicitly recognized above,
                // so that viewing a wit file on a terminal doesn't have surprising side
                // effects or appear to have a different meaning than its actual meaning.
                ch if ch.is_control() => {
                    bail!("control code '{}' at line {line}", ch.escape_unicode());
                }

                _ => {}
            }
        }

        Ok(())
    }
}

impl AstDisplay for Document<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        for (i, statement) in self.statements.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }

            statement.fmt(f, indenter)?;
            writeln!(f)?;
        }

        Ok(())
    }
}

display!(Document);

/// Represents a statement in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::Statement))]
pub struct Statement<'a> {
    /// The doc comments for the statement.
    pub docs: Vec<DocComment<'a>>,
    /// The statement kind.
    pub kind: StatementKind<'a>,
}

impl AstDisplay for Statement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        for doc in &self.docs {
            doc.fmt(f, indenter)?;
        }

        self.kind.fmt(f, indenter)
    }
}

display!(Statement);

/// Represents a statement kind in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::StatementKind))]
pub enum StatementKind<'a> {
    /// An import statement.
    Import(ImportStatement<'a>),
    /// A type statement.
    Type(TypeStatement<'a>),
    /// A let statement.
    Let(LetStatement<'a>),
    /// An export statement.
    Export(ExportStatement<'a>),
}

impl AstDisplay for StatementKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        match self {
            Self::Import(import) => import.fmt(f, indenter),
            Self::Type(ty) => ty.fmt(f, indenter),
            Self::Let(l) => l.fmt(f, indenter),
            Self::Export(export) => export.fmt(f, indenter),
        }
    }
}

display!(StatementKind);

/// Represents an identifier in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::Ident))]
pub struct Ident<'a>(#[pest_ast(outer())] pub Span<'a>);

impl Ident<'_> {
    /// Gets the identifier as a string.
    ///
    /// This trims any leading `%` character in a raw identifier.
    pub fn as_str(&self) -> &str {
        self.0.as_str().trim_start_matches('%')
    }
}

impl AstDisplay for Ident<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, _indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{s}", s = self.0.as_str())
    }
}

display!(Ident);

/// Represents a string in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::String))]
pub struct String<'a>(#[pest_ast(outer())] pub Span<'a>);

impl String<'_> {
    /// Gets a string representation without the surrounding quotes.
    pub fn as_str(&self) -> &str {
        self.0.as_str().trim_matches('"')
    }
}

impl AstDisplay for String<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, _indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{s}", s = self.0.as_str())
    }
}

display!(String);

/// Represents a documentation comment in the AST.
#[derive(Debug, Clone, FromPest)]
#[pest_ast(rule(Rule::DocComment))]
pub struct DocComment<'a>(#[pest_ast(outer())] pub Span<'a>);

impl DocComment<'_> {
    /// Gets the lines of the documentation comment.
    pub fn lines(&self) -> impl Iterator<Item = &str> {
        let mut s = self.0.as_str().trim();

        if s.starts_with("///") {
            s = &s[3..];
        } else if s.starts_with("/**") {
            // The string ends with "*/" so, the slice end is (3 + 2 - 1).
            s = &s[3..s.len() - 4];
        }

        s.lines().map(str::trim)
    }
}

impl AstDisplay for DocComment<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>, indenter: &mut Indenter) -> fmt::Result {
        write!(f, "{indenter}{span}", span = self.0.as_str())
    }
}

display!(DocComment);

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
    pub(crate) fn roundtrip<'a, T>(
        rule: T::Rule,
        input: &'a str,
        expected: &str,
    ) -> anyhow::Result<()>
    where
        T: from_pest::FromPest<'a, Rule = Rule> + fmt::Display,
        T::FatalError: std::error::Error + Send + Sync + 'static,
    {
        let mut pairs = DocumentParser::parse(rule, input)
            .map_err(|e| e.renamed_rules(|r| r.rename().to_owned()))
            .context("failed to parse input string")?;

        let statement = T::from_pest(&mut pairs)?;
        assert_eq!(statement.to_string(), expected, "unexpected AST output");
        Ok(())
    }

    #[test]
    fn document_roundtrip() {
        roundtrip::<Document>(
            Rule::Document,
            r#"/* ignore me */
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
            r#"/// Doc comment #1!
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
"#,
        )
        .unwrap();
    }
}
