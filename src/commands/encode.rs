use anyhow::{anyhow, bail, Context, Result};
use clap::Args;
use std::{
    fs,
    io::{IsTerminal, Write},
    path::PathBuf,
};
use wac_parser::{
    ast::Document, Composition, EncodingOptions, ErrorFormatter, FileSystemPackageResolver,
};
use wasmparser::{Validator, WasmFeatures};
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

/// Encodes a composition into a WebAssembly component.
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

    /// Whether to not to define referenced packages.
    ///
    /// If not specified, all referenced packages will be imported.
    #[clap(long)]
    pub define: bool,

    /// The path to write the output to.
    ///
    /// If not specified, the output will be written to stdout.
    #[clap(long, short = 'o')]
    pub output: Option<PathBuf>,

    /// The path to the composition file.
    #[clap(value_name = "PATH")]
    pub path: PathBuf,
}

impl EncodeCommand {
    /// Executes the command.
    pub async fn exec(self) -> Result<()> {
        log::debug!("executing encode command");

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

        if !self.wat && self.output.is_none() && std::io::stdout().is_terminal() {
            bail!("cannot print binary wasm output to a terminal; pass the `-t` flag to print the text format instead");
        }

        let mut bytes = resolved.encode(EncodingOptions {
            define_packages: self.define,
        })?;
        if !self.no_validate {
            Validator::new_with_features(WasmFeatures {
                component_model: true,
                ..Default::default()
            })
            .validate_all(&bytes)
            .context("failed to validate the encoded composition")?;
        }

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
