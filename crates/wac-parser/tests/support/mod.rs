use miette::{GraphicalReportHandler, GraphicalTheme, NamedSource, Report};
use std::path::Path;

pub fn fmt_err(e: impl Into<Report>, path: &Path, source: &str) -> String {
    let mut s = String::new();
    let e = e.into();
    GraphicalReportHandler::new()
        .with_cause_chain()
        .with_theme(GraphicalTheme::unicode_nocolor())
        .render_report(
            &mut s,
            e.with_source_code(NamedSource::new(path.to_string_lossy(), source.to_string()))
                .as_ref(),
        )
        .expect("failed to render diagnostic");
    s
}
