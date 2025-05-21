use crate::{ExternKind, ItemKind, SubtypeChecker, Types, WorldId};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// The result of validating a component against a target world.
pub type TargetValidationResult = Result<(), TargetValidationReport>;

/// The report of validating a component against a target world.
#[derive(Debug, Default)]
pub struct TargetValidationReport {
    /// Imports present in the component but not in the target world.
    imports_not_in_target: BTreeSet<String>,
    /// Exports not in the component but required by the target world.
    ///
    /// This is a mapping from the name of the missing export to the expected item kind.
    missing_exports: BTreeMap<String, ItemKind>,
    /// Mismatched types between the component and the target world.
    ///
    /// This is a mapping from name of the mismatched item to a tuple of
    /// the extern kind of the item and type error.
    mismatched_types: BTreeMap<String, (ExternKind, anyhow::Error)>,
}

impl From<TargetValidationReport> for TargetValidationResult {
    fn from(report: TargetValidationReport) -> TargetValidationResult {
        if report.imports_not_in_target.is_empty()
            && report.missing_exports.is_empty()
            && report.mismatched_types.is_empty()
        {
            Ok(())
        } else {
            Err(report)
        }
    }
}

impl fmt::Display for TargetValidationReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.imports_not_in_target.is_empty() {
            writeln!(
                f,
                "Imports present in the component but not in the target world:"
            )?;
            for import in &self.imports_not_in_target {
                writeln!(f, "  - {}", import)?;
            }
        }
        if !self.missing_exports.is_empty() {
            writeln!(
                f,
                "Exports required by target world but not present in the component:"
            )?;
            for (name, item_kind) in &self.missing_exports {
                writeln!(f, "  - {}: {:?}", name, item_kind)?;
            }
        }
        if !self.mismatched_types.is_empty() {
            writeln!(
                f,
                "Type mismatches between the target world and the component:"
            )?;
            for (name, (kind, error)) in &self.mismatched_types {
                writeln!(f, "  - {}: {:?} ({})", name, kind, error)?;
            }
        }
        Ok(())
    }
}

impl std::error::Error for TargetValidationReport {}

impl TargetValidationReport {
    /// Returns the set of imports present in the component but not in the target world.
    pub fn imports_not_in_target(&self) -> impl Iterator<Item = &str> {
        self.imports_not_in_target.iter().map(|s| s.as_str())
    }

    /// Returns the exports not in the component but required by the target world.
    pub fn missing_exports(&self) -> impl Iterator<Item = (&str, &ItemKind)> {
        self.missing_exports.iter().map(|(s, k)| (s.as_str(), k))
    }

    /// Returns the mismatched types between the component and the target world.
    pub fn mismatched_types(&self) -> impl Iterator<Item = (&str, &ExternKind, &anyhow::Error)> {
        self.mismatched_types
            .iter()
            .map(|(s, (k, e))| (s.as_str(), k, e))
    }
}

/// Validate whether the component conforms to the given world.
///
/// # Example
///
/// ```ignore
/// let mut types = Types::default();
///
/// let mut resolve = wit_parser::Resolve::new();
/// let pkg = resolve.push_dir(path_to_wit_dir)?.0;
/// let wit_bytes = wit_component::encode(&resolve, pkg)?;
/// let wit = Package::from_bytes("wit", None, wit_bytes, &mut types)?;
///
/// let component_bytes = std::fs::read(path_to_component)?;  
/// let component = Package::from_bytes("component", None, component_bytes, &mut types)?;
/// let wit_world = get_wit_world(&types, wit.ty())?;
///
/// validate_target(&types, wit_world, component.ty())?;
/// ```
pub fn validate_target(
    types: &Types,
    wit_world_id: WorldId,
    component_world_id: WorldId,
) -> TargetValidationResult {
    let component_world = &types[component_world_id];
    let wit_world = &types[wit_world_id];
    // The interfaces imported implicitly through uses.
    let implicit_imported_interfaces = wit_world.implicit_imported_interfaces(types);
    let mut cache = Default::default();
    let mut checker = SubtypeChecker::new(&mut cache);

    let mut report = TargetValidationReport::default();

    // The output is allowed to import a subset of the world's imports
    checker.invert();
    for (import, item_kind) in component_world.imports.iter() {
        let Some(expected) = implicit_imported_interfaces
            .get(import.as_str())
            .or_else(|| wit_world.imports.get(import))
        else {
            report.imports_not_in_target.insert(import.to_owned());
            continue;
        };

        if let Err(e) = checker.is_subtype(expected.promote(), types, *item_kind, types) {
            report
                .mismatched_types
                .insert(import.to_owned(), (ExternKind::Import, e));
        }
    }

    checker.revert();

    // The output must export every export in the world
    for (name, expected) in &wit_world.exports {
        let Some(export) = component_world.exports.get(name).copied() else {
            report.missing_exports.insert(name.to_owned(), *expected);
            continue;
        };

        if let Err(e) = checker.is_subtype(export, types, expected.promote(), types) {
            report
                .mismatched_types
                .insert(name.to_owned(), (ExternKind::Export, e));
        }
    }

    report.into()
}
