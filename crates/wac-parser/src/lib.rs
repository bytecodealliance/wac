//! A library for encoding and decoding WebAssembly compositions.

#![deny(missing_docs)]

pub mod ast;
pub mod lexer;
mod resolution;

pub use resolution::*;
