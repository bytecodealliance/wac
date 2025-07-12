use anyhow::{bail, Context, Result};
use clap::Args;
use std::{
    fs,
    path::{Path, PathBuf},
};
use wac_types::{validate_target, ItemKind, Package, Types, WorldId};

/// Verifies that a given WebAssembly component targets a world.
#[derive(Args)]
#[clap(disable_version_flag = true)]
pub struct TargetsCommand {
    /// The path to the component.
    #[clap(value_name = "COMPONENT_PATH")]
    pub component: PathBuf,
    /// The path to the WIT definition containing the world to target.
    #[clap(long, value_name = "WIT_PATH")]
    pub wit: PathBuf,
    /// The name of the world to target
    ///
    /// If the wit package only has one world definition, this does not need to be specified.
    #[clap(long)]
    pub world: Option<String>,
}

impl TargetsCommand {
    /// Executes the command.
    pub async fn exec(self) -> Result<()> {
        log::debug!("executing targets command");
        let mut types = Types::default();

        let wit_bytes = encode_wit_as_component(&self.wit)?;
        let wit = Package::from_bytes("wit", None, wit_bytes, &mut types)?;

        let component_bytes = fs::read(&self.component).with_context(|| {
            format!(
                "failed to read file `{path}`",
                path = self.component.display()
            )
        })?;
        let component = Package::from_bytes("component", None, component_bytes, &mut types)?;

        let wit = get_wit_world(&types, wit.ty(), self.world.as_deref())?;

        validate_target(&types, wit, component.ty())?;

        Ok(())
    }
}

/// Gets the selected world from the component encoded WIT package
fn get_wit_world(
    types: &Types,
    top_level_world: WorldId,
    world_name: Option<&str>,
) -> anyhow::Result<WorldId> {
    let top_level_world = &types[top_level_world];
    let world = match world_name {
        Some(world_name) => top_level_world
            .exports
            .get(world_name)
            .with_context(|| format!("wit package did not contain a world named '{world_name}'"))?,
        None if top_level_world.exports.len() == 1 => {
            top_level_world.exports.values().next().unwrap()
        }
        None if top_level_world.exports.len() > 1 => {
            bail!("wit package has multiple worlds, please specify one with the --world flag")
        }
        None => {
            bail!("wit package did not contain a world")
        }
    };
    let ItemKind::Type(wac_types::Type::World(world_id)) = world else {
        // We expect the top-level world to export a world type
        bail!("wit package was not encoded properly")
    };
    let wit_world = &types[*world_id];
    let world = wit_world.exports.values().next();
    let Some(ItemKind::Component(w)) = world else {
        // We expect the nested world type to export a component
        bail!("wit package was not encoded properly")
    };
    Ok(*w)
}

/// Encodes the wit package found at `path` into a component
fn encode_wit_as_component(path: &Path) -> anyhow::Result<Vec<u8>> {
    let mut resolve = wit_parser::Resolve::new();
    let pkg = if path.is_dir() {
        log::debug!(
            "loading WIT package from directory `{path}`",
            path = path.display()
        );

        let (pkg, _) = resolve.push_dir(path)?;
        pkg
    } else {
        resolve.push_path(path)?.0
    };
    let encoded = wit_component::encode(&resolve, pkg).with_context(|| {
        format!(
            "failed to encode WIT package from `{path}`",
            path = path.display()
        )
    })?;
    Ok(encoded)
}
