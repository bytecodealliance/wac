use anyhow::{Context, Result};
use clap::Args;
use std::{fs, path::PathBuf};
use wac_parser::ast::Document;

/// Parses a composition into a WebAssembly component.
#[derive(Args)]
#[clap(disable_version_flag = true)]
pub struct ParseCommand {
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

        let doc = Document::parse(&contents, &self.path)?;

        println!("{doc:#?}");

        Ok(())
    }
}
