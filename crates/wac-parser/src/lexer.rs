//! Module for the lexer implementation.

use logos::{Logos, SpannedIter};
use miette::SourceSpan;
use std::fmt;

fn to_source_span(span: logos::Span) -> SourceSpan {
    SourceSpan::new(span.start.into(), (span.end - span.start).into())
}

/// Represents a lexer error.
#[derive(thiserror::Error, Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Error {
    /// An unexpected token was encountered.
    #[default]
    #[error("unexpected token was encountered")]
    UnexpectedToken,
    /// An unterminated string was encountered.
    #[error("an unterminated string was encountered")]
    UnterminatedString,
    /// An unterminated comment was encountered.
    #[error("an unterminated comment was encountered")]
    UnterminatedComment,
    /// A disallowed bidirectional override codepoint was encountered.
    #[error("disallowed bidirectional override codepoint `{c}`", c = .0.escape_unicode())]
    DisallowedBidirectionalOverride(char),
    /// A discouraged Unicode codepoint was encountered.
    #[error("codepoint `{c}` is discouraged by Unicode", c = .0.escape_unicode())]
    DiscouragedUnicodeCodepoint(char),
    /// A disallowed control code was encountered.
    #[error("disallowed control code '{c}'", c = .0.escape_unicode())]
    DisallowedControlCode(char),
}

impl From<()> for Error {
    fn from(_: ()) -> Self {
        Error::UnexpectedToken
    }
}

fn detect_invalid_input(source: &str) -> Result<(), (Error, SourceSpan)> {
    for (offset, ch) in source.char_indices() {
        match ch {
            '\r' | '\t' | '\n' => {}

            // Bidirectional override codepoints can be used to craft source code that
            // appears to have a different meaning than its actual meaning. See
            // [CVE-2021-42574] for background and motivation.
            //
            // [CVE-2021-42574]: https://cve.mitre.org/cgi-bin/cvename.cgi?name=CVE-2021-42574
            '\u{202a}' | '\u{202b}' | '\u{202c}' | '\u{202d}' | '\u{202e}' | '\u{2066}'
            | '\u{2067}' | '\u{2068}' | '\u{2069}' => {
                return Err((
                    Error::DisallowedBidirectionalOverride(ch),
                    SourceSpan::new(offset.into(), ch.len_utf8().into()),
                ));
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
                return Err((
                    Error::DiscouragedUnicodeCodepoint(ch),
                    SourceSpan::new(offset.into(), ch.len_utf8().into()),
                ));
            }

            // Disallow control codes other than the ones explicitly recognized above,
            // so that viewing a wit file on a terminal doesn't have surprising side
            // effects or appear to have a different meaning than its actual meaning.
            ch if ch.is_control() => {
                return Err((
                    Error::DisallowedControlCode(ch),
                    SourceSpan::new(offset.into(), ch.len_utf8().into()),
                ));
            }

            _ => {}
        }
    }

    Ok(())
}

/// Represents a WAC token.
#[derive(Logos, Debug, Clone, Copy, PartialEq, Eq)]
#[logos(error = Error)]
#[logos(skip r"[ \t\r\n\f]+")]
#[logos(subpattern word = r"[a-z][a-z0-9]*|[A-Z][A-Z0-9]*")]
#[logos(subpattern id = r"%?(?&word)(-(?&word))*")]
#[logos(subpattern package_name = r"(?&id)(:(?&id))+")]
#[logos(subpattern semver = r"[0-9a-zA-Z-\.\+]+")]
pub enum Token {
    /// A comment.
    #[regex(r"//[^\n]*", logos::skip)]
    Comment,

    /// A block comment.
    #[token(r"/*", helpers::skip_block_comment)]
    BlockComment,

    /// An identifier.
    #[regex(r"(?&id)")]
    Ident,

    /// A string literal.
    #[token("\"", helpers::string)]
    String,

    /// A package name.
    #[regex(r"(?&package_name)(@(?&semver))?")]
    PackageName,

    /// A package path with optional semantic version.
    #[regex(r"(?&package_name)(/(?&id))+(@(?&semver))?")]
    PackagePath,

    /// The `import` keyword.
    #[token("import")]
    ImportKeyword,
    /// The `with` keyword.
    #[token("with")]
    WithKeyword,
    /// The `type` keyword.
    #[token("type")]
    TypeKeyword,
    /// The `tuple` keyword.
    #[token("tuple")]
    TupleKeyword,
    /// The `list` keyword.
    #[token("list")]
    ListKeyword,
    /// The `option` keyword.
    #[token("option")]
    OptionKeyword,
    /// The `result` keyword.
    #[token("result")]
    ResultKeyword,
    /// The `borrow` keyword.
    #[token("borrow")]
    BorrowKeyword,
    /// The `resource` keyword.
    #[token("resource")]
    ResourceKeyword,
    /// The `variant` keyword.
    #[token("variant")]
    VariantKeyword,
    /// The `record` keyword.
    #[token("record")]
    RecordKeyword,
    /// The `flags` keyword.
    #[token("flags")]
    FlagsKeyword,
    /// The `enum` keyword.
    #[token("enum")]
    EnumKeyword,
    /// The `func` keyword.
    #[token("func")]
    FuncKeyword,
    /// The `static` keyword.
    #[token("static")]
    StaticKeyword,
    /// The `constructor` keyword.
    #[token("constructor")]
    ConstructorKeyword,
    /// The `u8` keyword.
    #[token("u8")]
    U8Keyword,
    /// The `s8` keyword.
    #[token("s8")]
    S8Keyword,
    /// The `u16` keyword.
    #[token("u16")]
    U16Keyword,
    /// The `s16` keyword.
    #[token("s16")]
    S16Keyword,
    /// The `u32` keyword.
    #[token("u32")]
    U32Keyword,
    /// The `s32` keyword.
    #[token("s32")]
    S32Keyword,
    /// The `u64` keyword.
    #[token("u64")]
    U64Keyword,
    /// The `s64` keyword.
    #[token("s64")]
    S64Keyword,
    /// The `float32` keyword.
    #[token("float32")]
    Float32Keyword,
    /// The `float64` keyword.
    #[token("float64")]
    Float64Keyword,
    /// The `char` keyword.
    #[token("char")]
    CharKeyword,
    /// The `bool` keyword.
    #[token("bool")]
    BoolKeyword,
    /// The `string` keyword.
    #[token("string")]
    StringKeyword,
    /// The `interface` keyword.
    #[token("interface")]
    InterfaceKeyword,
    /// The `world` keyword.
    #[token("world")]
    WorldKeyword,
    /// The `export` keyword.
    #[token("export")]
    ExportKeyword,
    /// The `new` keyword.
    #[token("new")]
    NewKeyword,
    /// The `let` keyword.
    #[token("let")]
    LetKeyword,
    /// The `use` keyword.
    #[token("use")]
    UseKeyword,
    /// The `include` keyword.
    #[token("include")]
    IncludeKeyword,
    /// The `as` keyword.
    #[token("as")]
    AsKeyword,
    /// The `package` keyword.
    #[token("package")]
    PackageKeyword,
    /// The `targets` keyword.
    #[token("targets")]
    TargetsKeyword,

    /// The `;` symbol.
    #[token(";")]
    Semicolon,
    /// The `{` symbol.
    #[token("{")]
    OpenBrace,
    /// The `}` symbol.
    #[token("}")]
    CloseBrace,
    /// The `:` symbol.
    #[token(":")]
    Colon,
    /// The `=` symbol.
    #[token("=")]
    Equals,
    /// The `(` symbol.
    #[token("(")]
    OpenParen,
    /// The `)` symbol.
    #[token(")")]
    CloseParen,
    /// The `->` symbol.
    #[token("->")]
    Arrow,
    /// The `<` symbol.
    #[token("<")]
    OpenAngle,
    /// The `>` symbol.
    #[token(">")]
    CloseAngle,
    /// The `_` symbol.
    #[token("_")]
    Underscore,
    /// The `[` symbol.
    #[token("[")]
    OpenBracket,
    /// The `]` symbol.
    #[token("]")]
    CloseBracket,
    /// The `.` symbol.
    #[token(".")]
    Dot,
    /// The `...` symbol.
    #[token("...")]
    Ellipsis,
    /// The `,` symbol.
    #[token(",")]
    Comma,
    /// The `/` symbol.
    #[token("/")]
    Slash,
    /// The `@` symbol.
    #[token("@")]
    At,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Comment | Token::BlockComment => write!(f, "comment"),
            Token::Ident => write!(f, "identifier"),
            Token::String => write!(f, "string literal"),
            Token::PackageName => write!(f, "package name"),
            Token::PackagePath => write!(f, "package path"),
            Token::ImportKeyword => write!(f, "`import` keyword"),
            Token::WithKeyword => write!(f, "`with` keyword"),
            Token::TypeKeyword => write!(f, "`type` keyword"),
            Token::TupleKeyword => write!(f, "`tuple` keyword"),
            Token::ListKeyword => write!(f, "`list` keyword"),
            Token::OptionKeyword => write!(f, "`option` keyword"),
            Token::ResultKeyword => write!(f, "`result` keyword"),
            Token::BorrowKeyword => write!(f, "`borrow` keyword"),
            Token::ResourceKeyword => write!(f, "`resource` keyword"),
            Token::VariantKeyword => write!(f, "`variant` keyword"),
            Token::RecordKeyword => write!(f, "`record` keyword"),
            Token::FlagsKeyword => write!(f, "`flags` keyword"),
            Token::EnumKeyword => write!(f, "`enum` keyword"),
            Token::FuncKeyword => write!(f, "`func` keyword"),
            Token::StaticKeyword => write!(f, "`static` keyword"),
            Token::ConstructorKeyword => write!(f, "`constructor` keyword"),
            Token::U8Keyword => write!(f, "`u8` keyword"),
            Token::S8Keyword => write!(f, "`s8` keyword"),
            Token::U16Keyword => write!(f, "`u16` keyword"),
            Token::S16Keyword => write!(f, "`s16` keyword"),
            Token::U32Keyword => write!(f, "`u32` keyword"),
            Token::S32Keyword => write!(f, "`s32` keyword"),
            Token::U64Keyword => write!(f, "`u64` keyword"),
            Token::S64Keyword => write!(f, "`s64` keyword"),
            Token::Float32Keyword => write!(f, "`float32` keyword"),
            Token::Float64Keyword => write!(f, "`float64` keyword"),
            Token::CharKeyword => write!(f, "`char` keyword"),
            Token::BoolKeyword => write!(f, "`bool` keyword"),
            Token::StringKeyword => write!(f, "`string` keyword"),
            Token::InterfaceKeyword => write!(f, "`interface` keyword"),
            Token::WorldKeyword => write!(f, "`world` keyword"),
            Token::ExportKeyword => write!(f, "`export` keyword"),
            Token::NewKeyword => write!(f, "`new` keyword"),
            Token::LetKeyword => write!(f, "`let` keyword"),
            Token::UseKeyword => write!(f, "`use` keyword"),
            Token::IncludeKeyword => write!(f, "`include` keyword"),
            Token::AsKeyword => write!(f, "`as` keyword"),
            Token::PackageKeyword => write!(f, "`package` keyword"),
            Token::TargetsKeyword => write!(f, "`targets` keyword"),
            Token::Semicolon => write!(f, "`;`"),
            Token::OpenBrace => write!(f, "`{{`"),
            Token::CloseBrace => write!(f, "`}}`"),
            Token::Colon => write!(f, "`:`"),
            Token::Equals => write!(f, "`=`"),
            Token::OpenParen => write!(f, "`(`"),
            Token::CloseParen => write!(f, "`)`"),
            Token::Arrow => write!(f, "`->`"),
            Token::OpenAngle => write!(f, "`<`"),
            Token::CloseAngle => write!(f, "`>`"),
            Token::Underscore => write!(f, "`_`"),
            Token::OpenBracket => write!(f, "`[`"),
            Token::CloseBracket => write!(f, "`]`"),
            Token::Dot => write!(f, "`.`"),
            Token::Ellipsis => write!(f, "`...`"),
            Token::Comma => write!(f, "`,`"),
            Token::Slash => write!(f, "`/`"),
            Token::At => write!(f, "`@`"),
        }
    }
}

mod helpers {
    use super::{Error, Token};
    use logos::{FilterResult, Logos};

    /// Represents a WAC comment token.
    #[derive(Logos, Debug, Clone, Copy, PartialEq, Eq)]
    #[logos(error = Error)]
    #[logos(skip r"[ \t\n\f]+")]
    pub enum CommentToken<'a> {
        /// A comment.
        #[regex(r"//[^\n]*")]
        Comment(&'a str),

        /// A block comment.
        #[token(r"/*", block_comment)]
        BlockComment(&'a str),
    }

    pub fn string(lex: &mut logos::Lexer<Token>) -> Result<(), Error> {
        let remainder = lex.remainder();
        let len = remainder.find('"').ok_or(Error::UnterminatedString)?;
        lex.bump(len + 1 /* opening quote */);
        Ok(())
    }

    pub fn block_comment_length(bytes: &[u8]) -> Option<usize> {
        let mut iter = bytes.iter().copied().peekable();
        let mut depth = 1;
        let mut len = 0;
        while depth > 0 {
            len += 1;
            match iter.next()? {
                b'/' if iter.peek() == Some(&b'*') => {
                    depth += 1;
                    len += 1;
                    iter.next();
                }
                b'*' if iter.peek() == Some(&b'/') => {
                    depth -= 1;
                    len += 1;
                    iter.next();
                }
                _ => {}
            }
        }

        Some(len + 2 /* opening tokens */)
    }

    pub fn block_comment<'a>(
        lex: &mut logos::Lexer<'a, CommentToken<'a>>,
    ) -> Result<&'a str, Error> {
        let span = lex.span();
        match block_comment_length(lex.remainder().as_bytes()) {
            Some(len) => {
                let s = &lex.source()[span.start..span.start + len];
                lex.bump(len - 2 /* opening tokens */);
                Ok(s)
            }
            None => {
                lex.bump(lex.remainder().len());
                Err(Error::UnterminatedComment)
            }
        }
    }

    pub fn skip_block_comment(lex: &mut logos::Lexer<Token>) -> FilterResult<(), Error> {
        match block_comment_length(lex.remainder().as_bytes()) {
            Some(len) => {
                lex.bump(len - 2 /* opening tokens */);
                FilterResult::Skip
            }
            None => {
                lex.bump(lex.remainder().len());
                FilterResult::Error(Error::UnterminatedComment)
            }
        }
    }
}

/// The result type for the lexer.
pub type LexerResult<T> = Result<T, Error>;

/// Implements a WAC lexer.
pub struct Lexer<'a>(SpannedIter<'a, Token>);

impl<'a> Lexer<'a> {
    /// Creates a new lexer for the given source string.
    pub fn new(source: &'a str) -> Result<Self, (Error, SourceSpan)> {
        detect_invalid_input(source)?;
        Ok(Self(Token::lexer(source).spanned()))
    }

    /// Gets the source string of the given span.
    pub fn source(&self, span: SourceSpan) -> &'a str {
        &self.0.source()[span.offset()..span.offset() + span.len()]
    }

    /// Gets the current span of the lexer.
    pub fn span(&self) -> SourceSpan {
        let mut span = self.0.span();
        if span.end == self.0.source().len() {
            // Currently miette silently fails to display a label
            // if the span is at the end of the source; this means
            // we can't properly show the "end of input" span.
            // For now, have the span point at the last byte in the source.
            // See: https://github.com/zkat/miette/issues/219
            span.start -= 1;
            span.end = span.start + 1;
        }

        to_source_span(span)
    }

    /// Peeks at the next token.
    pub fn peek(&self) -> Option<(LexerResult<Token>, SourceSpan)> {
        let mut lexer = self.0.clone().spanned();
        lexer.next().map(|(r, s)| (r, to_source_span(s)))
    }

    /// Peeks at the token after the next token.
    pub fn peek2(&self) -> Option<(LexerResult<Token>, SourceSpan)> {
        let mut lexer = self.0.clone().spanned();
        lexer.next();
        lexer.next().map(|(r, s)| (r, to_source_span(s)))
    }

    /// Consumes available documentation comment tokens.
    pub fn comments<'b>(&'b self) -> Result<Vec<(&'a str, SourceSpan)>, (Error, SourceSpan)> {
        let mut comments = Vec::new();
        let mut lexer = self.0.clone().morph::<helpers::CommentToken>().spanned();
        while let Some((Ok(token), span)) = lexer.next() {
            match token {
                helpers::CommentToken::Comment(c) | helpers::CommentToken::BlockComment(c) => {
                    let c = if let Some(c) = c.strip_prefix("///") {
                        c.trim()
                    } else if let Some(c) = c.strip_prefix("/**") {
                        if c == "/" {
                            continue;
                        }
                        c.strip_suffix("*/").unwrap().trim()
                    } else {
                        continue;
                    };
                    comments.push((c, to_source_span(span)));
                }
            }
        }
        Ok(comments)
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = (LexerResult<Token>, SourceSpan);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(r, s)| (r, to_source_span(s)))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use logos::{Logos, Source};
    use std::{fmt, ops::Range};

    //use super::*;

    #[allow(clippy::type_complexity)]
    pub fn assert_lex<'a, Token>(
        source: &'a Token::Source,
        tokens: &[(
            Result<Token, Token::Error>,
            &'a <Token::Source as Source>::Slice,
            Range<usize>,
        )],
    ) where
        Token: Logos<'a> + fmt::Debug + PartialEq,
        Token::Extras: Default,
    {
        let mut lex = Token::lexer(source);

        for tuple in tokens {
            assert_eq!(
                &(lex.next().expect("unexpected end"), lex.slice(), lex.span()),
                tuple
            );
        }

        assert_eq!(lex.next(), None, "tokens remain");
    }

    #[test]
    fn comments() {
        assert_lex::<Token>(
            r#"
            //
            // comment
            /**/
            /* a block comment */
            /* a multi
               line comment
             */
            /* a /* /* deeply */ nested */ block comment */
            "#,
            &[],
        );
    }

    #[test]
    fn unterminated_comment() {
        let source = r#"/* /* unterminated */"#;

        assert_lex::<Token>(
            source,
            &[(
                Err(Error::UnterminatedComment),
                "/* /* unterminated */",
                0..21,
            )],
        );
    }

    #[test]
    fn ident() {
        assert_lex(
            r#"
            foo
            foo123
            f-b
            foo-bar123
            foo0123-bar0123-baz0123
            %interface
            foo123-BAR
            "#,
            &[
                (Ok(Token::Ident), "foo", 13..16),
                (Ok(Token::Ident), "foo123", 29..35),
                (Ok(Token::Ident), "f-b", 48..51),
                (Ok(Token::Ident), "foo-bar123", 64..74),
                (Ok(Token::Ident), "foo0123-bar0123-baz0123", 87..110),
                (Ok(Token::Ident), "%interface", 123..133),
                (Ok(Token::Ident), "foo123-BAR", 146..156),
            ],
        );
    }

    #[test]
    fn string() {
        assert_lex(
            r#"
            ""
            "foo"
            "foo  bar"
            "foo
            bar"
            "#,
            &[
                (Ok(Token::String), "\"\"", 13..15),
                (Ok(Token::String), "\"foo\"", 28..33),
                (Ok(Token::String), "\"foo  bar\"", 46..56),
                (Ok(Token::String), "\"foo\n            bar\"", 69..90),
            ],
        );
    }

    #[test]
    fn package_path() {
        assert_lex(
            r#"
foo:bar/baz/qux/jam
foo:bar:baz:qux/jam
foo:bar/baz@0.0.4
foo:bar/baz@1.2.3
foo:bar/baz@10.20.30
foo:bar/baz@1.1.2-prerelease+meta
foo:bar/baz@1.1.2+meta
foo:bar/baz@1.1.2+meta-valid
foo:bar/baz@1.0.0-alpha
foo:bar/baz@1.0.0-beta
foo:bar/baz@1.0.0-alpha.beta
foo:bar/baz@1.0.0-alpha.beta.1
foo:bar/baz@1.0.0-alpha.1
foo:bar/baz@1.0.0-alpha0.valid
foo:bar/baz@1.0.0-alpha.0valid
foo:bar/baz@1.0.0-alpha-a.b-c-somethinglong+build.1-aef.1-its-okay
foo:bar/baz@1.0.0-rc.1+build.1
foo:bar/baz@2.0.0-rc.1+build.123
foo:bar/baz@1.2.3-beta
foo:bar/baz@10.2.3-DEV-SNAPSHOT
foo:bar/baz@1.2.3-SNAPSHOT-123
foo:bar/baz@1.0.0
foo:bar/baz@2.0.0
foo:bar/baz@1.1.7
foo:bar/baz@2.0.0+build.1848
foo:bar/baz@2.0.1-alpha.1227
foo:bar/baz@1.0.0-alpha+beta
foo:bar/baz@1.2.3----RC-SNAPSHOT.12.9.1--.12+788
foo:bar/baz@1.2.3----R-S.12.9.1--.12+meta
foo:bar/baz@1.2.3----RC-SNAPSHOT.12.9.1--.12
foo:bar/baz@1.0.0+0.build.1-rc.10000aaa-kk-0.1
foo:bar/baz@99999999999999999999999.999999999999999999.99999999999999999
foo:bar/baz@1.0.0-0A.is.legal
"#,
            &[
                (Ok(Token::PackagePath), "foo:bar/baz/qux/jam", 1..20),
                (Ok(Token::PackagePath), "foo:bar:baz:qux/jam", 21..40),
                (Ok(Token::PackagePath), "foo:bar/baz@0.0.4", 41..58),
                (Ok(Token::PackagePath), "foo:bar/baz@1.2.3", 59..76),
                (Ok(Token::PackagePath), "foo:bar/baz@10.20.30", 77..97),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.1.2-prerelease+meta",
                    98..131,
                ),
                (Ok(Token::PackagePath), "foo:bar/baz@1.1.2+meta", 132..154),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.1.2+meta-valid",
                    155..183,
                ),
                (Ok(Token::PackagePath), "foo:bar/baz@1.0.0-alpha", 184..207),
                (Ok(Token::PackagePath), "foo:bar/baz@1.0.0-beta", 208..230),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.0.0-alpha.beta",
                    231..259,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.0.0-alpha.beta.1",
                    260..290,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.0.0-alpha.1",
                    291..316,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.0.0-alpha0.valid",
                    317..347,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.0.0-alpha.0valid",
                    348..378,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.0.0-alpha-a.b-c-somethinglong+build.1-aef.1-its-okay",
                    379..445,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.0.0-rc.1+build.1",
                    446..476,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@2.0.0-rc.1+build.123",
                    477..509,
                ),
                (Ok(Token::PackagePath), "foo:bar/baz@1.2.3-beta", 510..532),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@10.2.3-DEV-SNAPSHOT",
                    533..564,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.2.3-SNAPSHOT-123",
                    565..595,
                ),
                (Ok(Token::PackagePath), "foo:bar/baz@1.0.0", 596..613),
                (Ok(Token::PackagePath), "foo:bar/baz@2.0.0", 614..631),
                (Ok(Token::PackagePath), "foo:bar/baz@1.1.7", 632..649),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@2.0.0+build.1848",
                    650..678,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@2.0.1-alpha.1227",
                    679..707,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.0.0-alpha+beta",
                    708..736,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.2.3----RC-SNAPSHOT.12.9.1--.12+788",
                    737..785,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.2.3----R-S.12.9.1--.12+meta",
                    786..827,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.2.3----RC-SNAPSHOT.12.9.1--.12",
                    828..872,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.0.0+0.build.1-rc.10000aaa-kk-0.1",
                    873..919,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@99999999999999999999999.999999999999999999.99999999999999999",
                    920..992,
                ),
                (
                    Ok(Token::PackagePath),
                    "foo:bar/baz@1.0.0-0A.is.legal",
                    993..1022,
                ),
            ],
        );
    }

    #[test]
    fn keywords() {
        assert_lex(
            r#"
import
with
type
tuple
list
option
result
borrow
resource
variant
record
flags
enum
func
static
constructor
u8
s8
u16
s16
u32
s32
u64
s64
float32
float64
char
bool
string
interface
world
export
new
let
use
include
as
package
targets
            "#,
            &[
                (Ok(Token::ImportKeyword), "import", 1..7),
                (Ok(Token::WithKeyword), "with", 8..12),
                (Ok(Token::TypeKeyword), "type", 13..17),
                (Ok(Token::TupleKeyword), "tuple", 18..23),
                (Ok(Token::ListKeyword), "list", 24..28),
                (Ok(Token::OptionKeyword), "option", 29..35),
                (Ok(Token::ResultKeyword), "result", 36..42),
                (Ok(Token::BorrowKeyword), "borrow", 43..49),
                (Ok(Token::ResourceKeyword), "resource", 50..58),
                (Ok(Token::VariantKeyword), "variant", 59..66),
                (Ok(Token::RecordKeyword), "record", 67..73),
                (Ok(Token::FlagsKeyword), "flags", 74..79),
                (Ok(Token::EnumKeyword), "enum", 80..84),
                (Ok(Token::FuncKeyword), "func", 85..89),
                (Ok(Token::StaticKeyword), "static", 90..96),
                (Ok(Token::ConstructorKeyword), "constructor", 97..108),
                (Ok(Token::U8Keyword), "u8", 109..111),
                (Ok(Token::S8Keyword), "s8", 112..114),
                (Ok(Token::U16Keyword), "u16", 115..118),
                (Ok(Token::S16Keyword), "s16", 119..122),
                (Ok(Token::U32Keyword), "u32", 123..126),
                (Ok(Token::S32Keyword), "s32", 127..130),
                (Ok(Token::U64Keyword), "u64", 131..134),
                (Ok(Token::S64Keyword), "s64", 135..138),
                (Ok(Token::Float32Keyword), "float32", 139..146),
                (Ok(Token::Float64Keyword), "float64", 147..154),
                (Ok(Token::CharKeyword), "char", 155..159),
                (Ok(Token::BoolKeyword), "bool", 160..164),
                (Ok(Token::StringKeyword), "string", 165..171),
                (Ok(Token::InterfaceKeyword), "interface", 172..181),
                (Ok(Token::WorldKeyword), "world", 182..187),
                (Ok(Token::ExportKeyword), "export", 188..194),
                (Ok(Token::NewKeyword), "new", 195..198),
                (Ok(Token::LetKeyword), "let", 199..202),
                (Ok(Token::UseKeyword), "use", 203..206),
                (Ok(Token::IncludeKeyword), "include", 207..214),
                (Ok(Token::AsKeyword), "as", 215..217),
                (Ok(Token::PackageKeyword), "package", 218..225),
                (Ok(Token::TargetsKeyword), "targets", 226..233),
            ],
        );
    }

    #[test]
    fn symbols() {
        assert_lex(
            r#";{}:=()-><>_[]. ...,/@"#,
            &[
                (Ok(Token::Semicolon), ";", 0..1),
                (Ok(Token::OpenBrace), "{", 1..2),
                (Ok(Token::CloseBrace), "}", 2..3),
                (Ok(Token::Colon), ":", 3..4),
                (Ok(Token::Equals), "=", 4..5),
                (Ok(Token::OpenParen), "(", 5..6),
                (Ok(Token::CloseParen), ")", 6..7),
                (Ok(Token::Arrow), "->", 7..9),
                (Ok(Token::OpenAngle), "<", 9..10),
                (Ok(Token::CloseAngle), ">", 10..11),
                (Ok(Token::Underscore), "_", 11..12),
                (Ok(Token::OpenBracket), "[", 12..13),
                (Ok(Token::CloseBracket), "]", 13..14),
                (Ok(Token::Dot), ".", 14..15),
                (Ok(Token::Ellipsis), "...", 16..19),
                (Ok(Token::Comma), ",", 19..20),
                (Ok(Token::Slash), "/", 20..21),
                (Ok(Token::At), "@", 21..22),
            ],
        );
    }
}
