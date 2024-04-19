use std::{io::Write as _, path::PathBuf};

use anyhow::{Context as _, Result};
use clap::Args;
use wac_graph::{CompositionGraph, EncodeOptions};
use wac_types::{Package, SubtypeChecker};

/// Plugs the exports of any number of 'plug' components into the imports of a 'socket' component.
#[derive(Args)]
#[clap(disable_version_flag = true)]
pub struct PlugCommand {
    /// The path to the plug component
    pub plug: PathBuf,

    /// The path to the socket component
    pub socket: PathBuf,

    /// The path to write the output to.
    ///
    /// If not specified, the output will be written to stdout.
    #[clap(long, short = 'o')]
    pub output: Option<PathBuf>,
}

impl PlugCommand {
    /// Executes the command.
    pub async fn exec(&self) -> Result<()> {
        log::debug!("executing plug command");
        let mut graph = CompositionGraph::new();

        let plug = std::fs::read(&self.plug).with_context(|| {
            format!(
                "failed to read plug component `{path}`",
                path = self.plug.display()
            )
        })?;
        let socket = std::fs::read(&self.socket).with_context(|| {
            format!(
                "failed to read socket component `{path}`",
                path = self.plug.display()
            )
        })?;

        // Register the packages
        let plug = Package::from_bytes("plug", None, plug, graph.types_mut())?;
        let plug = graph.register_package(plug)?;
        let socket = Package::from_bytes("socket", None, socket, graph.types_mut())?;
        let socket = graph.register_package(socket)?;

        let socket_instantiation = graph.instantiate(socket);
        let plug_instantiation = graph.instantiate(plug);
        let mut plugs = Vec::new();
        let mut cache = Default::default();
        let mut checker = SubtypeChecker::new(&mut cache);
        for (name, plug_ty) in &graph.types()[graph[plug].ty()].exports {
            if let Some(socket_ty) = graph.types()[graph[socket].ty()].imports.get(name) {
                if let Ok(_) =
                    checker.is_subtype(*plug_ty, graph.types(), *socket_ty, graph.types())
                {
                    plugs.push(name.clone());
                }
            }
        }
        for plug in plugs {
            log::debug!("using export `{plug}` for plug");
            let export = graph.alias_instance_export(plug_instantiation, &plug)?;
            graph.set_instantiation_argument(socket_instantiation, &plug, export)?;
        }
        for name in graph.types()[graph[socket].ty()]
            .exports
            .keys()
            .cloned()
            .collect::<Vec<_>>()
        {
            let export = graph.alias_instance_export(socket_instantiation, &name)?;
            graph.export(export, &name)?;
        }

        let bytes = graph.encode(EncodeOptions::default())?;
        match &self.output {
            Some(path) => {
                std::fs::write(&path, bytes).context(format!(
                    "failed to write output file `{path}`",
                    path = path.display()
                ))?;
            }
            None => {
                std::io::stdout()
                    .write_all(&bytes)
                    .context("failed to write to stdout")?;
            }
        }
        Ok(())
    }
}
