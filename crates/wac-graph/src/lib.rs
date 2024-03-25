//! A library for defining, encoding, and decoding WebAssembly composition graphs.

#![deny(missing_docs)]

pub(crate) mod encoding;
mod graph;

pub use graph::*;
