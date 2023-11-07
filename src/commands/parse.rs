use anyhow::{anyhow, Context, Result};
use clap::Args;
use std::{fs, io::IsTerminal, path::PathBuf};
use wac_parser::{ast::Document, ErrorFormatter};

/// Parses a composition into a JSON AST representation.
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

        let document = Document::parse(&contents, &self.path).map_err(|e| {
            anyhow!(
                "{e}",
                e = ErrorFormatter::new(&self.path, e, std::io::stderr().is_terminal())
            )
        })?;

        serde_json::to_writer_pretty(std::io::stdout(), &document)?;
        println!();

        Ok(())
    }
}
