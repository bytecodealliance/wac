use crate::fmt_err;
use anyhow::{Context, Result};
use clap::Args;
use std::{fs, path::PathBuf};
use wac_parser::Document;

/// Parses a WAC source file into a JSON AST representation.
#[derive(Args)]
#[clap(disable_version_flag = true)]
pub struct ParseCommand {
    /// The path to the source WAC file.
    #[clap(value_name = "PATH")]
    pub path: PathBuf,
}

impl ParseCommand {
    /// Executes the command.
    pub async fn exec(self) -> Result<()> {
        log::debug!("executing parse command");

        let contents = fs::read_to_string(&self.path)
            .with_context(|| format!("failed to read file `{path}`", path = self.path.display()))?;

        let document = Document::parse(&contents).map_err(|e| fmt_err(e, &self.path, &contents))?;

        serde_json::to_writer_pretty(std::io::stdout(), &document)?;
        println!();

        Ok(())
    }
}
