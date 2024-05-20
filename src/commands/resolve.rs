use crate::{fmt_err, PackageResolver};
use anyhow::{Context, Result};
use clap::Args;
use std::{fs, path::PathBuf};
use wac_parser::Document;

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

/// Resolves a WAC source file into a DOT representation.
#[derive(Args)]
#[clap(disable_version_flag = true)]
pub struct ResolveCommand {
    /// The directory to search for package dependencies.
    #[clap(long, value_name = "PATH", default_value = "deps")]
    pub deps_dir: PathBuf,

    /// The directory to search for package dependencies.
    #[clap(long = "dep", short, value_name = "PKG=PATH", value_parser = parse::<String, PathBuf>)]
    pub deps: Vec<(String, PathBuf)>,

    /// The URL of the registry to use.
    #[cfg(feature = "registry")]
    #[clap(long, value_name = "URL")]
    pub registry: Option<String>,

    /// The path to the source WAC file.
    #[clap(value_name = "PATH")]
    pub path: PathBuf,
}

impl ResolveCommand {
    /// Executes the command.
    pub async fn exec(self) -> Result<()> {
        log::debug!("executing resolve command");

        let contents = fs::read_to_string(&self.path)
            .with_context(|| format!("failed to read file `{path}`", path = self.path.display()))?;

        let document = Document::parse(&contents).map_err(|e| fmt_err(e, &self.path, &contents))?;

        let mut resolver = PackageResolver::new(
            self.deps_dir,
            self.deps.into_iter().collect(),
            #[cfg(feature = "registry")]
            self.registry.as_deref(),
        )
        .await?;

        let packages = resolver
            .resolve(&document)
            .await
            .map_err(|e| fmt_err(e, &self.path, &contents))?;

        let resolution = document
            .resolve(packages)
            .map_err(|e| fmt_err(e, &self.path, &contents))?;

        print!("{:?}", resolution.into_graph());

        Ok(())
    }
}
