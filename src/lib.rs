//! A library for encoding and decoding WebAssembly compositions.

#![deny(missing_docs)]

use miette::{GraphicalReportHandler, GraphicalTheme, NamedSource, Report};
use std::{io::IsTerminal, path::Path};

pub mod commands;

fn fmt_err(e: impl Into<Report>, path: &Path, source: &str) -> anyhow::Error {
    let mut s = String::new();
    let e = e.into();
    GraphicalReportHandler::new()
        .with_cause_chain()
        .with_theme(if std::io::stderr().is_terminal() {
            GraphicalTheme::unicode()
        } else {
            GraphicalTheme::unicode_nocolor()
        })
        .render_report(
            &mut s,
            e.with_source_code(NamedSource::new(path.to_string_lossy(), source.to_string()))
                .as_ref(),
        )
        .expect("failed to render diagnostic");
    anyhow::Error::msg(s)
}
