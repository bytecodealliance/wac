use anyhow::Result;
use clap::Parser;
use dialoguer::{theme::ColorfulTheme, Confirm};
use owo_colors::{OwoColorize, Stream, Style};
use wac_cli::commands::{EncodeCommand, ParseCommand, ResolveCommand};
use wac_resolver::CommandError;
use warg_client::{with_interactive_retry, ClientError, Retry};

fn version() -> &'static str {
    option_env!("CARGO_VERSION_INFO").unwrap_or(env!("CARGO_PKG_VERSION"))
}

/// Tool for working with WebAssembly compositions.
#[derive(Parser)]
#[clap(
    bin_name = "wac",
    version,
    propagate_version = true,
    arg_required_else_help = true
)]
#[command(version = version())]
enum Wac {
    Parse(ParseCommand),
    Resolve(ResolveCommand),
    Encode(EncodeCommand),
}

#[tokio::main]
async fn main() -> Result<()> {
    pretty_env_logger::init();

    with_interactive_retry(|retry: Option<Retry>| async {
        if let Err(err) = match Wac::parse() {
            Wac::Parse(cmd) => cmd.exec().await,
            Wac::Resolve(cmd) => cmd.exec(retry).await,
            Wac::Encode(cmd) => cmd.exec(retry).await,
        } {
            if let CommandError::WargHint(ClientError::PackageDoesNotExistWithHint { name, hint }) = &err {
                if let Some((namespace, registry)) = hint.to_str().unwrap().split_once('=') {
                    let prompt = format!(
                      "The package `{}`, does not exist in the registry you're using.
                      However, the package namespace `{namespace}` does exist in the registry at {registry}.
                      Would you like to configure your warg cli to use this registry for packages with this namespace in the future? y/N\n",
                      name.name(),
                    );
                    if Confirm::with_theme(&ColorfulTheme::default())
                        .with_prompt(prompt)
                        .interact()
                        .unwrap()
                    {
                        if let Err(e) = match Wac::parse() {
                          Wac::Parse(cmd) => cmd.exec().await,
                          Wac::Resolve(cmd) => {
                              cmd.exec(Some(Retry::new(
                                                namespace.to_string(),
                                                registry.to_string(),
                                            )))
                                            .await
                          },
                          Wac::Encode(cmd) => {
                              cmd.exec(Some(Retry::new(
                                namespace.to_string(),
                                registry.to_string(),
                            )))
                                .await
                          },
                        }
                          {
                        eprintln!(
                          "{error}: {e:?}",
                          error = "error".if_supports_color(Stream::Stderr, |text| {
                              text.style(Style::new().red().bold())
                          })
                      );
                      std::process::exit(1);
                        }
                    }
                }
            }

            eprintln!(
                "{error}: {err:?}",
                error = "error".if_supports_color(Stream::Stderr, |text| {
                    text.style(Style::new().red().bold())
                })
            );
            std::process::exit(1);
        }
        Ok(())
    })
    .await?;
    Ok(())
}
