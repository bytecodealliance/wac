//! The keywords in the AST.

use super::serialize_span;
use crate::parser::Rule;
use pest::Span;
use pest_ast::FromPest;
use serde::Serialize;
use std::fmt;

macro_rules! keywords {
    ($(($id:ident, $rule:path, $name:literal)),* $(,)?) => {
        $(
            #[doc = concat!("Represents the `", $name, "` keyword in the AST.")]
            #[derive(Debug, Clone, Copy, Serialize, FromPest)]
            #[pest_ast(rule($rule))]
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
                crate::ast::test::roundtrip::<$id>($rule, $name, $name).unwrap();
            }
        )*
        }
    };
}

keywords!(
    (Import, Rule::ImportKeyword, "import"),
    (With, Rule::WithKeyword, "with"),
    (Type, Rule::TypeKeyword, "type"),
    (Tuple, Rule::TupleKeyword, "tuple"),
    (List, Rule::ListKeyword, "list"),
    (Option, Rule::OptionKeyword, "option"),
    (Result, Rule::ResultKeyword, "result"),
    (Borrow, Rule::BorrowKeyword, "borrow"),
    (Resource, Rule::ResourceKeyword, "resource"),
    (Variant, Rule::VariantKeyword, "variant"),
    (Record, Rule::RecordKeyword, "record"),
    (Flags, Rule::FlagsKeyword, "flags"),
    (Enum, Rule::EnumKeyword, "enum"),
    (Func, Rule::FuncKeyword, "func"),
    (Static, Rule::StaticKeyword, "static"),
    (Constructor, Rule::ConstructorKeyword, "constructor"),
    (U8, Rule::U8Keyword, "u8"),
    (S8, Rule::S8Keyword, "s8"),
    (U16, Rule::U16Keyword, "u16"),
    (S16, Rule::S16Keyword, "s16"),
    (U32, Rule::U32Keyword, "u32"),
    (S32, Rule::S32Keyword, "s32"),
    (U64, Rule::U64Keyword, "u64"),
    (S64, Rule::S64Keyword, "s64"),
    (Float32, Rule::Float32Keyword, "float32"),
    (Float64, Rule::Float64Keyword, "float64"),
    (Char, Rule::CharKeyword, "char"),
    (Bool, Rule::BoolKeyword, "bool"),
    (String, Rule::StringKeyword, "string"),
    (Interface, Rule::InterfaceKeyword, "interface"),
    (World, Rule::WorldKeyword, "world"),
    (Export, Rule::ExportKeyword, "export"),
    (New, Rule::NewKeyword, "new"),
    (Let, Rule::LetKeyword, "let"),
    (Use, Rule::UseKeyword, "use"),
    (Include, Rule::IncludeKeyword, "include"),
    (As, Rule::AsKeyword, "as"),
);
