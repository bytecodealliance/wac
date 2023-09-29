//! The symbols in the AST.

use super::serialize_span;
use crate::parser::Rule;
use pest::Span;
use pest_ast::FromPest;
use serde::Serialize;
use std::fmt;

macro_rules! symbols {
    ($(($id:ident, $name:literal)),* $(,)?) => {
        $(
            #[doc = concat!("Represents the `", $name, "` symbol in the AST.")]
            #[derive(Debug, Clone, Copy, Serialize, FromPest)]
            #[pest_ast(rule(Rule::$id))]
            pub struct $id<'a>(#[pest_ast(outer())] #[serde(serialize_with = "serialize_span")] pub Span<'a>);

            impl fmt::Display for $id<'_> {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    write!(f, "{span}", span = self.0.as_str())
                }
            }
        )*

        #[cfg(test)]
        mod test {
            use super::*;

        $(
            #[test]
            #[allow(non_snake_case)]
            fn $id() {
                crate::ast::test::roundtrip::<$id>(Rule::$id, $name, $name).unwrap();
            }
        )*
        }
    };
}

symbols!(
    (Semicolon, ";"),
    (OpenBrace, "{"),
    (CloseBrace, "}"),
    (Colon, ":"),
    (Equals, "="),
    (OpenParen, "("),
    (CloseParen, ")"),
    (Arrow, "->"),
    (OpenAngle, "<"),
    (CloseAngle, ">"),
    (Percent, "%"),
    (Underscore, "_"),
    (Hyphen, "-"),
    (DoubleQuote, "\""),
    (Slash, "/"),
    (At, "@"),
    (OpenBracket, "["),
    (CloseBracket, "]"),
    (Dot, "."),
    (Ellipsis, "..."),
);
