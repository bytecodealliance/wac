//! A library for encoding and decoding WebAssembly compositions.

#![deny(missing_docs)]

mod ast;
pub mod lexer;
pub mod resolution;

pub use ast::*;
