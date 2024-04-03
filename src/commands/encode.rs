use crate::{fmt_err, PackageResolver};
use anyhow::{bail, Context, Result};
use clap::Args;
use std::{
    fs,
    io::{IsTerminal, Write},
    path::PathBuf,
};
use wac_graph::EncodeOptions;
use wac_parser::Document;
use wasmprinter::print_bytes;

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

/// Encodes a WAC source file into a WebAssembly component.
#[derive(Args)]
#[clap(disable_version_flag = true)]
pub struct EncodeCommand {
    /// The directory to search for package dependencies.
    #[clap(long, value_name = "PATH", default_value = "deps")]
    pub deps_dir: PathBuf,

    /// The directory to search for package dependencies.
    #[clap(long = "dep", short, value_name = "PKG=PATH", value_parser = parse::<String, PathBuf>)]
    pub deps: Vec<(String, PathBuf)>,

    /// Whether to skip validation of the encoded WebAssembly component.
    #[clap(long)]
    pub no_validate: bool,

    /// Whether to emit the WebAssembly text format.
    #[clap(long, short = 't')]
    pub wat: bool,

    /// Whether the composed component imports its dependencies.
    ///
    /// If false, all referenced dependent packages will be defined within the component.
    ///
    /// Defaults to false.
    #[clap(long, short)]
    pub import_dependencies: bool,

    /// The path to write the output to.
    ///
    /// If not specified, the output will be written to stdout.
    #[clap(long, short = 'o')]
    pub output: Option<PathBuf>,

    /// The URL of the registry to use.
    #[cfg(feature = "registry")]
    #[clap(long, value_name = "URL")]
    pub registry: Option<String>,

    /// The path to the source file.
    #[clap(value_name = "PATH")]
    pub path: PathBuf,
}

impl EncodeCommand {
    /// Executes the command.
    pub async fn exec(self) -> Result<()> {
        log::debug!("executing encode command");

        let contents = fs::read_to_string(&self.path)
            .with_context(|| format!("failed to read file `{path}`", path = self.path.display()))?;

        let document = Document::parse(&contents).map_err(|e| fmt_err(e, &self.path, &contents))?;

        let resolver = PackageResolver::new(
            self.deps_dir,
            self.deps.into_iter().collect(),
            #[cfg(feature = "registry")]
            self.registry.as_deref(),
        )?;

        let packages = resolver
            .resolve(&document)
            .await
            .map_err(|e| fmt_err(e, &self.path, &contents))?;

        let resolution = document
            .resolve(packages)
            .map_err(|e| fmt_err(e, &self.path, &contents))?;

        if !self.wat && self.output.is_none() && std::io::stdout().is_terminal() {
            bail!("cannot print binary wasm output to a terminal; pass the `-t` flag to print the text format instead");
        }

        let mut bytes = resolution.encode(EncodeOptions {
            define_components: !self.import_dependencies,
            validate: !self.no_validate,
            ..Default::default()
        })?;
        if self.wat {
            bytes = print_bytes(&bytes)
                .context("failed to convert binary wasm output to text")?
                .into_bytes();
        }

        match self.output {
            Some(path) => {
                fs::write(&path, bytes).context(format!(
                    "failed to write output file `{path}`",
                    path = path.display()
                ))?;
            }
            None => {
                std::io::stdout()
                    .write_all(&bytes)
                    .context("failed to write to stdout")?;

                if self.wat {
                    println!();
                }
            }
        }

        Ok(())
    }
}
