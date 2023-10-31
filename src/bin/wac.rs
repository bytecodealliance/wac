use anyhow::Result;
use clap::Parser;
use owo_colors::{OwoColorize, Stream, Style};
use wac::commands::ParseCommand;

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
}

#[tokio::main]
async fn main() -> Result<()> {
    pretty_env_logger::init();

    if let Err(e) = match Wac::parse() {
        Wac::Parse(cmd) => cmd.exec().await,
    } {
        eprintln!(
            "{error}: {e:?}",
            error = "error".if_supports_color(Stream::Stderr, |text| {
                text.style(Style::new().red().bold())
            })
        );
        std::process::exit(1);
    }

    Ok(())
}
