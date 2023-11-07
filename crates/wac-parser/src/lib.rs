//! A library for encoding and decoding WebAssembly compositions.

#![deny(missing_docs)]

use anyhow::Chain;
use lexer::Span;
use owo_colors::{OwoColorize, Style};
use std::{
    fmt::{self, Write},
    path::Path,
};

pub mod ast;
pub mod lexer;
pub mod printer;
pub mod resolution;

/// Gets the 1-based line and column of a position within a source.
pub(crate) fn line_column(source: &str, pos: usize) -> (usize, usize) {
    let mut cur = 0;
    // Use split_terminator instead of lines so that if there is a `\r`,
    // it is included in the offset calculation. The `+1` values below
    // account for the `\n`.
    for (i, line) in source.split_terminator('\n').enumerate() {
        if cur + line.len() + 1 > pos {
            return (i + 1, pos - cur + 1);
        }

        cur += line.len() + 1;
    }

    (source.lines().count() + 1, 1)
}

/// Implemented on spanned error types.
pub trait Spanned {
    /// Gets the span of the error.
    fn span(&self) -> Span;
}

/// A formatter for spanned errors.
pub struct ErrorFormatter<P, E> {
    path: P,
    error: E,
    colorize: bool,
}

impl<P, E> ErrorFormatter<P, E>
where
    P: AsRef<Path>,
    E: std::error::Error + Spanned,
{
    /// Creates a new error formatter.
    pub fn new(path: P, error: E, colorize: bool) -> Self {
        Self {
            path,
            error,
            colorize,
        }
    }
}

struct Indented<'a, D> {
    inner: &'a mut D,
    number: Option<usize>,
    started: bool,
}

// Copied from anyhow's error formatter
// https://github.com/dtolnay/anyhow/blob/05e413219e97f101d8f39a90902e5c5d39f951fe/src/fmt.rs#L73
impl<T> Write for Indented<'_, T>
where
    T: Write,
{
    fn write_str(&mut self, s: &str) -> fmt::Result {
        for (i, line) in s.split('\n').enumerate() {
            if !self.started {
                self.started = true;
                match self.number {
                    Some(number) => write!(self.inner, "{: >5}: ", number)?,
                    None => self.inner.write_str("    ")?,
                }
            } else if i > 0 {
                self.inner.write_char('\n')?;
                if self.number.is_some() {
                    self.inner.write_str("       ")?;
                } else {
                    self.inner.write_str("    ")?;
                }
            }

            self.inner.write_str(line)?;
        }

        Ok(())
    }
}

impl<P, E> fmt::Display for ErrorFormatter<P, E>
where
    P: AsRef<Path>,
    E: std::error::Error + Spanned,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let span = self.error.span();
        let (line, column) = line_column(span.source(), span.start);
        let snippet = span.source().lines().nth(line - 1).unwrap_or("");

        let (bold, blue) = if self.colorize {
            (Style::new().bold(), Style::new().blue().bold())
        } else {
            (Style::new(), Style::new())
        };

        write!(
            f,
            "{error}\n    {arrow} {path}:{lineno}:{column}\n     {bar}\n{line:4} {bar} {snippet}\n     {bar} {marker:>0$}",
            column,
            error = self.error.style(bold),
            arrow = "-->".style(blue),
            path = self.path.as_ref().display(),
            lineno = line,
            bar = "|".style(blue),
            line = line.style(blue),
            marker = "^".style(blue),
        )?;

        if let Some(s) = span.source().get(span.start..span.end) {
            for _ in s.chars().skip(2) {
                write!(f, "{}", "-".style(blue))?;
            }

            if s.len() > 1 {
                write!(f, "{}", "^".style(blue))?;
            }
        }

        writeln!(f)?;

        if let Some(cause) = self.error.source() {
            write!(f, "\nCaused by:")?;
            let multiple = cause.source().is_some();
            for (n, error) in Chain::new(cause).enumerate() {
                writeln!(f)?;
                let mut indented = Indented {
                    inner: f,
                    number: if multiple { Some(n) } else { None },
                    started: false,
                };
                write!(indented, "{}", error)?;
            }
        }

        Ok(())
    }
}
