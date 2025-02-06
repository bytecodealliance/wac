use anyhow::{bail, Context, Result};
use clap::Args;
use std::{
    fs,
    path::{Path, PathBuf},
};
use wac_types::{ExternKind, ItemKind, Package, SubtypeChecker, Types, WorldId};

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

/// An error in target validation
#[derive(thiserror::Error, miette::Diagnostic, Debug)]
#[diagnostic(code("component does not match wit world"))]
pub enum Error {
    #[error("the target wit does not have an import named `{import}` but the component does")]
    /// The import is not in the target world
    ImportNotInTarget {
        /// The name of the missing target
        import: String,
    },
    #[error("{kind} `{name}` has a mismatched type for targeted wit world")]
    /// An import or export has a mismatched type for the target world.
    TargetMismatch {
        /// The name of the mismatched item
        name: String,
        /// The extern kind of the item
        kind: ExternKind,
        /// The source of the error
        #[source]
        source: anyhow::Error,
    },
    #[error("the targeted wit world requires an export named `{name}` but the component did not export one")]
    /// Missing an export for the target world.
    MissingTargetExport {
        /// The export name.
        name: String,
        /// The expected item kind.
        kind: ItemKind,
    },
}

/// Validate whether the component conforms to the given world
pub fn validate_target(
    types: &Types,
    wit_world_id: WorldId,
    component_world_id: WorldId,
) -> Result<(), Error> {
    let component_world = &types[component_world_id];
    let wit_world = &types[wit_world_id];
    // The interfaces imported implicitly through uses.
    let implicit_imported_interfaces = wit_world.implicit_imported_interfaces(types);
    let mut cache = Default::default();
    let mut checker = SubtypeChecker::new(&mut cache);

    // The output is allowed to import a subset of the world's imports
    checker.invert();
    for (import, item_kind) in component_world.imports.iter() {
        let expected = implicit_imported_interfaces
            .get(import.as_str())
            .or_else(|| wit_world.imports.get(import))
            .ok_or_else(|| Error::ImportNotInTarget {
                import: import.to_owned(),
            })?;

        checker
            .is_subtype(expected.promote(), types, *item_kind, types)
            .map_err(|e| Error::TargetMismatch {
                kind: ExternKind::Import,
                name: import.to_owned(),
                source: e,
            })?;
    }

    checker.revert();

    // The output must export every export in the world
    for (name, expected) in &wit_world.exports {
        let export = component_world.exports.get(name).copied().ok_or_else(|| {
            Error::MissingTargetExport {
                name: name.clone(),
                kind: *expected,
            }
        })?;

        checker
            .is_subtype(export, types, expected.promote(), types)
            .map_err(|e| Error::TargetMismatch {
                kind: ExternKind::Export,
                name: name.clone(),
                source: e,
            })?;
    }

    Ok(())
}
