use anyhow::{anyhow, Context, Result};
use clap::Args;
use std::{fs, io::IsTerminal, path::PathBuf};
use wac_parser::{ast::Document, Composition, ErrorFormatter, FileSystemPackageResolver};

fn parse<T, U>(s: &str) -> Result<(T, U)>
where
    T: std::str::FromStr,
    T::Err: Into<anyhow::Error>,
    U: std::str::FromStr,
    U::Err: Into<anyhow::Error>,
{
    let (k, v) = s.split_once('=').context("value does not contain `=`")?;

    Ok((
        k.trim().parse().map_err(Into::into)?,
        v.trim().parse().map_err(Into::into)?,
    ))
}

/// Resolves a composition into a JSON representation.
#[derive(Args)]
#[clap(disable_version_flag = true)]
pub struct ResolveCommand {
    /// The directory to search for package dependencies.
    #[clap(long, value_name = "PATH", default_value = "deps")]
    pub deps_dir: PathBuf,

    /// The directory to search for package dependencies.
    #[clap(long = "dep", short, value_name = "PKG=PATH", value_parser = parse::<String, PathBuf>)]
    pub deps: Vec<(String, PathBuf)>,

    /// The path to the composition file.
    #[clap(value_name = "PATH")]
    pub path: PathBuf,
}

impl ResolveCommand {
    /// Executes the command.
    pub async fn exec(self) -> Result<()> {
        log::debug!("executing resolve command");

        let contents = fs::read_to_string(&self.path)
            .with_context(|| format!("failed to read file `{path}`", path = self.path.display()))?;

        let document = Document::parse(&contents, &self.path).map_err(|e| {
            anyhow!(
                "{e}",
                e = ErrorFormatter::new(&self.path, e, std::io::stderr().is_terminal())
            )
        })?;

        let resolved = Composition::from_ast(
            &document,
            Some(Box::new(FileSystemPackageResolver::new(
                self.deps_dir,
                self.deps.into_iter().collect(),
            ))),
        )
        .map_err(|e| {
            anyhow!(
                "{e}",
                e = ErrorFormatter::new(&self.path, e, std::io::stderr().is_terminal())
            )
        })?;

        serde_json::to_writer_pretty(std::io::stdout(), &resolved)?;
        println!();

        Ok(())
    }
}
