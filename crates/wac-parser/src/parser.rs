//! Module for the parser implementation.

#[allow(missing_docs)]
mod pest {
    use pest_derive::Parser;

    /// Implements a WAC document parser.
    #[derive(Parser)]
    #[grammar = "../wac.pest"]
    pub struct DocumentParser;

    impl Rule {
        /// Renames a rule to a more human-readable name.
        pub fn rename(&self) -> &str {
            match self {
                Self::EOI => "end of input",
                Self::WHITESPACE | Self::DelimitingSpace => "whitespace",
                Self::COMMENT => "comment",

                Self::DocComment => "documentation comment",
                Self::LineComment => "line comment",
                Self::BlockComment => "block comment",

                Self::Document | Self::Statement | Self::StatementKind => "statement",
                Self::ImportStatement => "import statement",
                Self::TypeStatement => "type statement",
                Self::ValueTypeStatement => "value type statement",
                Self::ResourceDecl => "resource declaration",
                Self::ResourceBody => "resource body",
                Self::VariantDecl => "variant declaration",
                Self::VariantBody => "variant body",
                Self::VariantCase => "variant case",
                Self::VariantType => "variant type",
                Self::RecordDecl => "record declaration",
                Self::RecordBody => "record body",
                Self::FlagsDecl => "flags declaration",
                Self::FlagsBody => "flags body",
                Self::EnumDecl => "enum declaration",
                Self::EnumBody => "enum body",
                Self::TypeAlias => "type alias",
                Self::InterfaceDecl => "interface declaration",
                Self::WorldDecl => "world declaration",
                Self::LetStatement => "let statement",
                Self::ExportStatement => "export statement",

                Self::ImportType => "import type",
                Self::WithClause => "with clause",
                Self::PackagePath => "package path",
                Self::PackageName => "package name",
                Self::PackageVersion => "package version",

                Self::TypeAliasKind => "type alias",
                Self::FuncType => "function type",
                Self::Type | Self::OmitType => "value type",
                Self::Tuple => "tuple",
                Self::List => "list",
                Self::Option => "option",
                Self::Result => "result",
                Self::SpecifiedResult => "specified result",
                Self::Borrow => "borrow",

                Self::ResourceMethod => "resource method",
                Self::Constructor => "constructor",
                Self::Method => "method",
                Self::FuncTypeRef => "function type reference",
                Self::ParamList => "parameter list",
                Self::ResultList => "result list",
                Self::NamedResultList => "named result list",
                Self::NamedType => "name and type",

                Self::UseStatement => "use statement",
                Self::UseItems => "use items",
                Self::UsePath => "use path",

                Self::InterfaceBody => "interface body",
                Self::InterfaceItem => "interface item",
                Self::InterfaceItemKind => "interface item kind",
                Self::InterfaceExportStatement => "interface export statement",

                Self::WorldBody => "world body",
                Self::WorldItem => "world item",
                Self::WorldItemKind => "world item kind",
                Self::WorldImportStatement => "world import statement",
                Self::WorldExportStatement => "world export statement",
                Self::WorldItemDecl => "world item declaration",
                Self::WorldNamedItem => "world named item",
                Self::InterfaceRef => "interface reference",
                Self::ExternType => "extern type",
                Self::InlineInterface => "inline interface",

                Self::WorldIncludeStatement => "world include statement",
                Self::WorldIncludeWithClause => "world include with clause",
                Self::WorldIncludeItem => "world include item",
                Self::WorldRef => "world reference",

                Self::Expr => "expression",
                Self::PrimaryExpr => "primary expression",
                Self::NewExpr => "new expression",
                Self::NewExprBody => "new expression body",
                Self::InstantiationArgument => "instantiation argument",
                Self::NamedInstantiationArgument => "named instantiation argument",
                Self::NestedExpr => "nested expression",
                Self::PostfixExpr => "postfix expression",
                Self::AccessExpr => "access expression",
                Self::NamedAccessExpr => "named access expression",

                Self::RawIdent => "raw identifier",
                Self::Ident => "identifier",
                Self::IdentPart => "identifier part",

                Self::String => "string",

                Self::Keyword => "keyword",
                Self::WithKeyword => "`with` keyword",
                Self::ImportKeyword => "`import` keyword",
                Self::TupleKeyword => "`tuple` keyword",
                Self::ListKeyword => "`list` keyword",
                Self::OptionKeyword => "`option` keyword",
                Self::ResultKeyword => "`result` keyword",
                Self::BorrowKeyword => "`borrow` keyword",
                Self::ResourceKeyword => "`resource` keyword",
                Self::VariantKeyword => "`variant` keyword",
                Self::RecordKeyword => "`record` keyword",
                Self::FlagsKeyword => "`flags` keyword",
                Self::EnumKeyword => "`enum` keyword",
                Self::FuncKeyword => "`func` keyword",
                Self::StaticKeyword => "`static` keyword",
                Self::ConstructorKeyword => "`constructor` keyword",
                Self::TypeKeyword => "`type` keyword",
                Self::U8Keyword => "`u8` keyword",
                Self::S8Keyword => "`s8` keyword",
                Self::U16Keyword => "`u16` keyword",
                Self::S16Keyword => "`s16` keyword",
                Self::U32Keyword => "`u32` keyword",
                Self::S32Keyword => "`s32` keyword",
                Self::U64Keyword => "`u64` keyword",
                Self::S64Keyword => "`s64` keyword",
                Self::Float32Keyword => "`float32` keyword",
                Self::Float64Keyword => "`float64` keyword",
                Self::CharKeyword => "`char` keyword",
                Self::BoolKeyword => "`bool` keyword",
                Self::StringKeyword => "`string` keyword",
                Self::InterfaceKeyword => "`interface` keyword",
                Self::WorldKeyword => "`world` keyword",
                Self::ExportKeyword => "`export` keyword",
                Self::NewKeyword => "`new` keyword",
                Self::LetKeyword => "`let` keyword",
                Self::UseKeyword => "`use` keyword",
                Self::IncludeKeyword => "`include` keyword",
                Self::AsKeyword => "`as` keyword",

                Self::Semicolon => "`;`",
                Self::OpenBrace => "`{`",
                Self::CloseBrace => "`}`",
                Self::Colon => "`:`",
                Self::Equals => "`=`",
                Self::OpenParen => "`(`",
                Self::CloseParen => "`)`",
                Self::Arrow => "`->`",
                Self::OpenAngle => "`<`",
                Self::CloseAngle => "`>`",
                Self::Percent => "`%`",
                Self::Underscore => "`_`",
                Self::Hyphen => "`-`",
                Self::DoubleQuote => "`\"`",
                Self::Slash => "`/`",
                Self::At => "`@`",
                Self::OpenBracket => "`[`",
                Self::CloseBracket => "`]`",
                Self::Dot => "`.`",
                Self::Ellipsis => "`...`",
            }
        }
    }
}

pub use pest::DocumentParser;
pub use pest::Rule;
