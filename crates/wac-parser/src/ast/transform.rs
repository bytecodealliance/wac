use super::{parse_token, Error, Lookahead, PackageName, Parse, ParseResult, Peek};
use crate::lexer::{to_source_span, Lexer, Token};
use miette::SourceSpan;
use serde::{Serialize, Serializer};
use wasm_wave::{
    parser::{Parser, ParserError},
    untyped::UntypedValue,
};

/// Represents the application of a component transformer.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Transform<'a> {
    /// The span of the `transform` keyword.
    pub span: SourceSpan,
    /// The package name corresponding to the transformer component.
    pub transformer: PackageName<'a>,
    /// The component to be transformed.
    pub component: PackageName<'a>,
    /// The configuration argument provided to the transformer.
    #[serde(serialize_with = "serialize_display")]
    pub untyped_value: UntypedValue<'a>,
}

impl<'a> Parse<'a> for Transform<'a> {
    fn parse(lexer: &mut Lexer<'a>) -> ParseResult<Self> {
        let span = parse_token(lexer, Token::TransformKeyword)?;
        parse_token(lexer, Token::OpenAngle)?;
        let transformer = Parse::parse(lexer)?;
        parse_token(lexer, Token::CloseAngle)?;
        let component = Parse::parse(lexer)?;

        // Ensure the WAVE value begins with an open-curly brace.
        let mut lookahead = Lookahead::new(lexer);
        if !lookahead.peek(Token::OpenBrace) {
            return Err(lookahead.error());
        }

        // Morph the WAC token stream into a WAVE lexer.
        let morphed = (*lexer.0).clone().morph();
        let mut parser = Parser::with_lexer(morphed);

        let untyped_value = parser.parse_raw_value()?;

        // Bump the WAC lexer by the consumed length of the WAVE value.
        let len = untyped_value.node().span().end - lexer.0.span().end;
        (*lexer.0).bump(len);

        Ok(Transform {
            span,
            transformer,
            component,
            untyped_value,
        })
    }
}

impl Peek for Transform<'_> {
    fn peek(lookahead: &mut Lookahead) -> bool {
        lookahead.peek(Token::TransformKeyword)
    }
}

impl From<ParserError> for Error {
    fn from(err: ParserError) -> Self {
        // TODO: better handling of converting WAVE errors to WAC errors.
        Self::InvalidValue {
            error: err.kind(),
            detail: err.detail().unwrap_or("").to_string(),
            span: to_source_span(err.span()),
        }
    }
}

fn serialize_display<V, S>(value: &V, serializer: S) -> Result<S::Ok, S::Error>
where
    V: ::std::fmt::Display,
    S: Serializer,
{
    serializer.collect_str(value)
}
