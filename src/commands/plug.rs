use std::{
    io::{IsTerminal as _, Write as _},
    path::PathBuf,
};

use anyhow::{bail, Context as _, Error, Result};
use clap::Args;
use std::str::FromStr;
use wac_graph::{CompositionGraph, EncodeOptions, NodeId, PackageId};
use wac_types::{Package, SubtypeChecker};

#[cfg(feature = "registry")]
use warg_client::FileSystemClient;

#[cfg(feature = "registry")]
use warg_protocol::registry::PackageName;

/// The package path or registry package name.
#[derive(Clone, Debug)]
pub enum PackageRef {
    /// The local file path to the component.
    LocalPath(PathBuf),
    /// The registry package name.
    #[cfg(feature = "registry")]
    RegistryPackage((PackageName, Option<semver::Version>)),
}

impl FromStr for PackageRef {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        #[cfg(feature = "registry")]
        return Ok(s
            .split_once('@')
            .map(|(name, version)| {
                match (PackageName::new(name), semver::Version::parse(version)) {
                    (Ok(name), Ok(ver)) => Ok(Some(Self::RegistryPackage((name, Some(ver))))),
                    (Ok(_), Err(e)) => bail!("invalid version for package `{s}`: {e}"),
                    (Err(_), _) => Ok(None),
                }
            })
            .unwrap_or(Ok(None))?
            .unwrap_or_else(|| match PackageName::new(s) {
                Ok(name) => Self::RegistryPackage((name, None)),
                _ => Self::LocalPath(PathBuf::from(s)),
            }));

        #[cfg(not(feature = "registry"))]
        Ok(Self::LocalPath(PathBuf::from(s)))
    }
}

impl std::fmt::Display for PackageRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LocalPath(path) => write!(f, "{}", path.display()),
            #[cfg(feature = "registry")]
            Self::RegistryPackage((name, Some(ver))) => write!(f, "{}@{}", name, ver),
            #[cfg(feature = "registry")]
            Self::RegistryPackage((name, None)) => write!(f, "{}", name),
        }
    }
}

/// Plugs the exports of any number of 'plug' components into the imports of a 'socket' component.
#[derive(Args)]
#[clap(disable_version_flag = true)]
pub struct PlugCommand {
    /// The local path to the plug component or the registry package name.
    ///
    /// More than one plug can be supplied.
    #[clap(long = "plug", value_name = "PLUG_PATH", required = true)]
    pub plugs: Vec<PackageRef>,

    /// The local path to the socket component or the registry package name.
    #[clap(value_name = "SOCKET_PATH", required = true)]
    pub socket: PackageRef,

    /// Whether to emit the WebAssembly text format.
    #[clap(long, short = 't')]
    pub wat: bool,

    /// The path to write the output to.
    ///
    /// If not specified, the output will be written to stdout.
    #[clap(long, short = 'o')]
    pub output: Option<PathBuf>,

    /// The URL of the registry to use.
    #[cfg(feature = "registry")]
    #[clap(long, value_name = "URL")]
    pub registry: Option<String>,
}

impl PlugCommand {
    /// Executes the command.
    pub async fn exec(&self) -> Result<()> {
        log::debug!("executing plug command");
        let mut graph = CompositionGraph::new();

        #[cfg(feature = "registry")]
        let client = FileSystemClient::new_with_default_config(self.registry.as_deref()).ok();

        let socket_path = match &self.socket {
            #[cfg(feature = "registry")]
            PackageRef::RegistryPackage((name, version)) => {
                let client = client.as_ref().ok_or_else(|| {
                    anyhow::anyhow!(
                        "Warg registry is not configured. Package `{name}` was not found."
                    )
                })?;

                if let Some(ver) = version {
                    let download = client.download_exact(name, ver).await?;
                    log::debug!(
                        "Plugging `{name}` version `{ver}` using registry `{registry}`",
                        registry = client.url()
                    );
                    download.path
                } else {
                    let download = client
                        .download(name, &semver::VersionReq::STAR)
                        .await?
                        .ok_or_else(|| anyhow::anyhow!("package `{name}` was not found"))?;

                    log::debug!(
                        "Plugging `{name}` version `{ver}` using registry `{registry}`",
                        ver = &download.version,
                        registry = client.url()
                    );
                    download.path
                }
            }
            PackageRef::LocalPath(path) => {
                log::debug!("Plugging `{path}`", path = path.display());

                path.clone()
            }
        };
        let socket = std::fs::read(socket_path).with_context(|| {
            format!(
                "failed to read socket component `{socket}`",
                socket = self.socket
            )
        })?;

        let socket = Package::from_bytes("socket", None, socket, graph.types_mut())?;
        let socket = graph.register_package(socket)?;
        let socket_instantiation = graph.instantiate(socket);

        // Collect the plugs by their names
        let mut plugs_by_name = std::collections::HashMap::<_, Vec<_>>::new();
        for plug in self.plugs.iter() {
            let name = match plug {
                #[cfg(feature = "registry")]
                PackageRef::RegistryPackage((name, _)) => std::borrow::Cow::Borrowed(name.as_ref()),
                PackageRef::LocalPath(path) => path
                    .file_stem()
                    .map(|fs| fs.to_string_lossy())
                    .with_context(|| format!("path to plug '{}' was not a file", plug))?,
            };

            // TODO(rylev): sanitize the name to ensure it's a valid package identifier.
            plugs_by_name.entry(name).or_default().push(plug);
        }

        // Plug each plug into the socket.
        for (name, plug_refs) in plugs_by_name {
            for (i, plug_ref) in plug_refs.iter().enumerate() {
                let (mut name, path) = match plug_ref {
                    #[cfg(feature = "registry")]
                    PackageRef::RegistryPackage((name, version)) => {
                        let client = client.as_ref().ok_or_else(|| {
                            anyhow::anyhow!(
                                "Warg registry is not configured. Package `{name}` was not found."
                            )
                        })?;

                        let path = if let Some(ver) = version {
                            let download = client.download_exact(name, ver).await?;
                            log::debug!(
                                "    with `{name}` version `{ver}` using registry `{registry}`",
                                registry = client.url()
                            );
                            download.path
                        } else {
                            let download = client
                                .download(name, &semver::VersionReq::STAR)
                                .await?
                                .ok_or_else(|| anyhow::anyhow!("package `{name}` was not found"))?;

                            log::debug!(
                                "    with `{name}` version `{ver}` using registry `{registry}`",
                                ver = &download.version,
                                registry = client.url()
                            );
                            download.path
                        };

                        let name = name.as_ref().to_string();
                        (name, path)
                    }
                    PackageRef::LocalPath(path) => {
                        log::debug!("    with `{path}`", path = path.display());
                        (format!("plug:{name}"), path.clone())
                    }
                };
                // If there's more than one plug with the same name, append an index to the name.
                if plug_refs.len() > 1 {
                    use core::fmt::Write;
                    write!(&mut name, "{i}").unwrap();
                }
                plug_into_socket(&name, &path, socket, socket_instantiation, &mut graph)?;
            }
        }

        // Check we've actually done any plugging.
        if graph
            .get_instantiation_arguments(socket_instantiation)
            .next()
            .is_none()
        {
            bail!("the socket component had no matching imports for the plugs that were provided")
        }

        // Export all exports from the socket component.
        for name in graph.types()[graph[socket].ty()]
            .exports
            .keys()
            .cloned()
            .collect::<Vec<_>>()
        {
            let export = graph.alias_instance_export(socket_instantiation, &name)?;
            graph.export(export, &name)?;
        }

        let binary_output_to_terminal =
            !self.wat && self.output.is_none() && std::io::stdout().is_terminal();
        if binary_output_to_terminal {
            bail!("cannot print binary wasm output to a terminal; pass the `-t` flag to print the text format instead");
        }

        let mut bytes = graph.encode(EncodeOptions::default())?;
        if self.wat {
            bytes = wasmprinter::print_bytes(&bytes)
                .context("failed to convert binary wasm output to text")?
                .into_bytes();
        }
        match &self.output {
            Some(path) => {
                std::fs::write(path, bytes).context(format!(
                    "failed to write output file `{path}`",
                    path = path.display()
                ))?;
                log::debug!("\nWrote plugged component: `{path}`", path = path.display());
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

/// Take the exports of the plug component and plug them into the socket component.
fn plug_into_socket(
    name: &str,
    plug_path: &std::path::Path,
    socket: PackageId,
    socket_instantiation: NodeId,
    graph: &mut CompositionGraph,
) -> Result<(), anyhow::Error> {
    let plug = Package::from_file(name, None, plug_path, graph.types_mut())?;
    let plug = graph.register_package(plug)?;

    let mut plugs = Vec::new();
    let mut cache = Default::default();
    let mut checker = SubtypeChecker::new(&mut cache);
    for (name, plug_ty) in &graph.types()[graph[plug].ty()].exports {
        if let Some(socket_ty) = graph.types()[graph[socket].ty()].imports.get(name) {
            if checker
                .is_subtype(*plug_ty, graph.types(), *socket_ty, graph.types())
                .is_ok()
            {
                plugs.push(name.clone());
            }
        }
    }

    // Instantiate the plug component
    let mut plug_instantiation = None;
    for plug_name in plugs {
        log::debug!("using export `{plug_name}` for plug");
        let plug_instantiation = *plug_instantiation.get_or_insert_with(|| graph.instantiate(plug));
        let export = graph.alias_instance_export(plug_instantiation, &plug_name)?;
        graph.set_instantiation_argument(socket_instantiation, &plug_name, export)?;
    }
    Ok(())
}
