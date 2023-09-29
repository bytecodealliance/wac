use anyhow::{Context, Result};
use clap::Args;
use serde::Serialize;
use std::{fs, path::PathBuf};
use wac_parser::{ast::Document, resolution::ResolvedDocument};

#[derive(Serialize)]
struct Output<'a> {
    ast: &'a Document<'a>,
    resolved: &'a ResolvedDocument<'a>,
}

/// Parses a composition into a WebAssembly component.
#[derive(Args)]
#[clap(disable_version_flag = true)]
pub struct ParseCommand {
    /// The package being parsed.
    #[clap(long, short, value_name = "PACKAGE")]
    pub package: String,

    /// The path to the composition file.
    #[clap(value_name = "PATH")]
    pub path: PathBuf,
}

impl ParseCommand {
    /// Executes the command.
    pub async fn exec(self) -> Result<()> {
        log::debug!("executing parse command");

        let contents = fs::read_to_string(&self.path)
            .with_context(|| format!("failed to read file `{path}`", path = self.path.display()))?;

        let document = Document::parse(&contents, &self.path)?;
        let resolved = ResolvedDocument::new(&document, self.package, None)?;

        serde_json::to_writer_pretty(
            std::io::stdout(),
            &Output {
                ast: &document,
                resolved: &resolved,
            },
        )?;
        println!();

        Ok(())
    }
}
