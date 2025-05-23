//! A library for the definition of WebAssembly component model types.

#![deny(missing_docs)]

mod aggregator;
mod checker;
mod component;
mod core;
mod package;
mod targets;

pub use aggregator::*;
pub use checker::*;
pub use component::*;
pub use core::*;
pub use package::*;
pub use targets::*;
