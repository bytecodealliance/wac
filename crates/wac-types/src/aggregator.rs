use crate::{
    names::{alternate_lookup_key, are_semver_compatible, is_label},
    DefinedType, DefinedTypeId, FuncType, FuncTypeId, Interface, InterfaceId, ItemKind,
    ModuleTypeId, Record, Resource, ResourceAlias, ResourceId, SubtypeChecker, Type, Types,
    UsedType, ValueType, Variant, World, WorldId,
};
use anyhow::{bail, Context, Result};
use indexmap::IndexMap;
use std::collections::HashMap;

/// Used to aggregate types defined in different `Types` collections.
///
/// A type aggregator can be used to merge compatible definitions of
/// the same type into a single supertype definition stored within the
/// aggregator; this is useful for imports that are shared across
/// different instantiation arguments.
///
/// It works by first recursively remapping a type from a foreign `Types`
/// collection into its own `Types` collection; any further attempt
/// to aggregate the type causes a merge of type definitions provided
/// they are compatible.
#[derive(Default, Debug)]
pub struct TypeAggregator {
    /// The aggregated types collection.
    types: Types,
    /// The map from import name to aggregated item kind.
    imports: IndexMap<String, ItemKind>,
    /// A map from foreign type to remapped local type.
    remapped: HashMap<Type, Type>,
    /// A map of interface names to remapped interface id.
    interfaces: HashMap<String, InterfaceId>,
    /// Maps import names that were superseded by a higher semver-compatible
    /// version to the canonical (highest version) name.
    name_redirects: HashMap<String, String>,
}

impl TypeAggregator {
    /// Creates a new type aggregator.
    pub fn new() -> Self {
        Self::default()
    }

    /// Gets the aggregator's type collection.
    pub fn types(&self) -> &Types {
        &self.types
    }

    /// Iterates the imported types in the aggregator.
    pub fn imports(&self) -> impl Iterator<Item = (&str, ItemKind)> {
        self.imports.iter().map(|(n, k)| (n.as_str(), *k))
    }

    /// Returns the canonical (highest semver version) import name for the given name.
    ///
    /// If the name was superseded by a higher semver-compatible version,
    /// the canonical name is returned. Otherwise, the name itself is returned.
    pub fn canonical_import_name<'a>(&'a self, name: &'a str) -> &'a str {
        self.name_redirects
            .get(name)
            .map(|s| s.as_str())
            .unwrap_or(name)
    }

    /// Finds an import whose name is on a compatible semver track with `name`.
    ///
    /// Returns both the existing import name and its `ItemKind`.
    fn find_semver_compatible_import(&self, name: &str) -> Option<(&str, ItemKind)> {
        let (alt_key, _) = alternate_lookup_key(name)?;
        for (existing_name, kind) in &self.imports {
            if let Some((existing_alt, _)) = alternate_lookup_key(existing_name) {
                if existing_alt == alt_key {
                    return Some((existing_name.as_str(), *kind));
                }
            }
        }
        None
    }

    /// Finds an interface whose name is on a compatible semver track with `name`.
    fn find_semver_compatible_interface(&self, name: &str) -> Option<InterfaceId> {
        let (alt_key, _) = alternate_lookup_key(name)?;
        for (existing_name, id) in &self.interfaces {
            if let Some((existing_alt, _)) = alternate_lookup_key(existing_name) {
                if existing_alt == alt_key {
                    return Some(*id);
                }
            }
        }
        None
    }

    /// Aggregates a item kind from a specified type collection using the given
    /// import name.
    ///
    /// Note that if the aggregate operation fails, the aggregator is consumed.
    pub fn aggregate(
        mut self,
        name: &str,
        types: &Types,
        kind: ItemKind,
        checker: &mut SubtypeChecker,
    ) -> Result<Self> {
        // First check if this import has already been remapped into our
        // types collection.
        // If it has already been remapped, do a merge; otherwise, remap it.
        if let Some(existing) = self.imports.get(name).copied() {
            self.merge_item_kind(existing, types, kind, checker)?;
            return Ok(self);
        }

        // Check for a semver-compatible import (e.g., a:b/c@0.2.0 matching a:b/c@0.2.1)
        if let Some((existing_name, existing_kind)) = self.find_semver_compatible_import(name) {
            // Copy values before the mutable borrow in merge_item_kind
            let existing_name = existing_name.to_string();
            self.merge_item_kind(existing_kind, types, kind, checker)?;
            let (_, new_version) = alternate_lookup_key(name).unwrap();
            let (_, existing_version) = alternate_lookup_key(&existing_name).unwrap();

            if new_version > existing_version {
                // New version is higher: remove old entry, insert new name
                let merged_kind = self.imports.shift_remove(&existing_name).unwrap();
                self.imports.insert(name.to_string(), merged_kind);
                // Update any existing redirects that pointed to the old name
                for redirect in self.name_redirects.values_mut() {
                    if *redirect == existing_name {
                        *redirect = name.to_string();
                    }
                }
                self.name_redirects.insert(existing_name, name.to_string());
            } else {
                // Existing version is higher or equal: redirect new name to existing
                self.name_redirects.insert(name.to_string(), existing_name);
            }

            return Ok(self);
        }

        let remapped = self.remap_extern(name, types, kind, checker)?;
        let prev = self.imports.insert(name.to_string(), remapped);
        assert!(prev.is_none());
        Ok(self)
    }

    fn merge_item_kind(
        &mut self,
        existing: ItemKind,
        types: &Types,
        kind: ItemKind,
        checker: &mut SubtypeChecker,
    ) -> Result<()> {
        match (existing, kind) {
            (ItemKind::Instance(existing), ItemKind::Instance(id)) => {
                self.merge_interface(existing, types, id, checker)
            }
            (ItemKind::Component(existing), ItemKind::Component(id)) => {
                self.merge_world(existing, types, id, checker)
            }
            (ItemKind::Func(existing), ItemKind::Func(id)) => {
                self.merge_func_type(existing, types, id, checker)
            }
            (ItemKind::Module(existing), ItemKind::Module(id)) => {
                self.merge_module_type(existing, types, id, checker)
            }
            (ItemKind::Type(existing), ItemKind::Type(ty)) => {
                self.merge_type(existing, types, ty, checker)
            }
            (ItemKind::Value(existing), ItemKind::Value(ty)) => {
                self.merge_value_type(existing, types, ty, checker)
            }
            (existing, kind) => {
                bail!(
                    "{existing} cannot be merged with {kind}",
                    existing = existing.desc(&self.types),
                    kind = kind.desc(types)
                );
            }
        }
    }

    fn merge_interface(
        &mut self,
        existing: InterfaceId,
        types: &Types,
        id: InterfaceId,
        checker: &mut SubtypeChecker,
    ) -> Result<()> {
        self.merge_interface_names(existing, types, id)?;

        // Merge the used types of the two interfaces
        self.merge_interface_used_types(existing, types, id, checker)?;

        // Merge the interface's exports
        for (name, source_kind) in &types[id].exports {
            let mut merged_name = None;
            if let Some(target_kind) = self.types[existing].exports.get(name).copied() {
                if let (true, ItemKind::Instance(target), ItemKind::Instance(source)) =
                    (is_label(name), target_kind, *source_kind)
                {
                    self.merge_interface_names(target, types, source)?;
                    merged_name = Some(self.types[target].id.clone());
                }
                // If the source kind is already a subtype of the target, do nothing
                if checker
                    .is_subtype(*source_kind, types, target_kind, &self.types)
                    .is_ok()
                {
                    // Labelled instances have a separate definition per extern.
                    // Caching their mapping would make a later named import
                    // reuse this label's potentially narrower definition.
                    if !(is_label(name) && matches!(source_kind, ItemKind::Instance(_))) {
                        self.remapped.insert(source_kind.ty(), target_kind.ty());
                    }
                    continue;
                }

                // Otherwise, the target *must* be a subtype of the source
                // We'll remap the source below and replace
                checker
                    .is_subtype(target_kind, &self.types, *source_kind, types)
                    .with_context(|| format!("mismatched type for export `{name}`"))?;
            }

            let remapped = self.remap_extern(name, types, *source_kind, checker)?;
            if let (Some(name), ItemKind::Instance(id)) = (merged_name, remapped) {
                self.types[id].id = name;
            }
            self.types[existing].exports.insert(name.clone(), remapped);
        }

        Ok(())
    }

    /// Checks that two named interfaces being merged are the same interface on
    /// compatible semver tracks, and names the merged interface after the
    /// higher version.
    ///
    /// The merged interface can have exports only the higher version defines,
    /// and an `(implements "I")` import of it encodes its name as `I`.
    ///
    /// Merging a named interface with an unnamed one (e.g. a label imported
    /// both as `(implements "I")` and as an inline interface) keeps the name,
    /// whichever is merged first.
    fn merge_interface_names(
        &mut self,
        existing: InterfaceId,
        types: &Types,
        id: InterfaceId,
    ) -> Result<()> {
        let (existing_name, name) = match (&self.types[existing].id, &types[id].id) {
            (Some(existing_name), Some(name)) => (existing_name, name),
            (None, Some(name)) => {
                self.types[existing].id = Some(name.clone());
                return Ok(());
            }
            _ => return Ok(()),
        };

        if !are_semver_compatible(existing_name, name) {
            bail!("interface `{name}` cannot be merged with interface `{existing_name}`");
        }

        if let (Some((_, existing_version)), Some((_, version))) = (
            alternate_lookup_key(existing_name),
            alternate_lookup_key(name),
        ) {
            if version > existing_version {
                self.types[existing].id = Some(name.clone());
            }
        }

        Ok(())
    }

    fn merge_interface_used_types(
        &mut self,
        existing: InterfaceId,
        types: &Types,
        id: InterfaceId,
        checker: &mut SubtypeChecker,
    ) -> Result<()> {
        let source = &types[id];
        for (name, used) in &source.uses {
            let used_interface = types[used.interface]
                .id
                .as_ref()
                .context("used type has no interface identifier")?;

            // Validate any existing used type of the same name
            if let Some(existing) = self.types[existing].uses.get(name) {
                let existing_interface = self.types[existing.interface]
                    .id
                    .as_ref()
                    .context("used type has no interface identifier")?;

                // The interface names must be on compatible semver tracks
                if !are_semver_compatible(existing_interface, used_interface) {
                    bail!("cannot merge used type `{name}` as it is expected to be from interface `{existing_interface}` but it is from interface `{used_interface}`");
                }

                // The types must be exported with the same name
                if existing.name != used.name {
                    bail!("cannot merge used type `{name}` as the export names are mismatched");
                }
            }

            // Remap the used interface; this will handle merging if we've seen the interface before
            let remapped = self.remap_interface(types, used.interface, checker)?;
            match self.types[existing].uses.get(name) {
                Some(existing) => {
                    assert_eq!(
                        existing.interface, remapped,
                        "expected a merge to have occurred"
                    );
                }
                None => {
                    self.types[existing].uses.insert(
                        name.clone(),
                        UsedType {
                            interface: remapped,
                            name: used.name.clone(),
                        },
                    );
                }
            }
        }

        Ok(())
    }

    fn merge_world(
        &mut self,
        existing: WorldId,
        types: &Types,
        id: WorldId,
        checker: &mut SubtypeChecker,
    ) -> Result<()> {
        // Merge the used types of the two worlds
        self.merge_world_used_types(existing, types, id, checker)?;

        // Merge the worlds's imports
        checker.invert();
        for (name, source_kind) in &types[id].imports {
            let mut merged_name = None;
            if let Some(target_kind) = self.types[existing].imports.get(name).copied() {
                if let (true, ItemKind::Instance(target), ItemKind::Instance(source)) =
                    (is_label(name), target_kind, *source_kind)
                {
                    self.merge_interface_names(target, types, source)?;
                    merged_name = Some(self.types[target].id.clone());
                }
                // If the target kind is already a subtype of the source, do nothing
                if checker
                    .is_subtype(target_kind, &self.types, *source_kind, types)
                    .is_ok()
                {
                    continue;
                }

                // Otherwise, the source *must* be a subtype of the target
                // We'll remap the source below and replace
                checker
                    .is_subtype(*source_kind, types, target_kind, &self.types)
                    .with_context(|| format!("mismatched type for import `{name}`"))?;
            }

            let remapped = self.remap_extern(name, types, *source_kind, checker)?;
            if let (Some(name), ItemKind::Instance(id)) = (merged_name, remapped) {
                self.types[id].id = name;
            }
            self.types[existing].imports.insert(name.clone(), remapped);
        }

        checker.revert();

        // Merge the worlds's exports
        for (name, source_kind) in &types[id].exports {
            let mut merged_name = None;
            if let Some(target_kind) = self.types[existing].exports.get(name).copied() {
                if let (true, ItemKind::Instance(target), ItemKind::Instance(source)) =
                    (is_label(name), target_kind, *source_kind)
                {
                    self.merge_interface_names(target, types, source)?;
                    merged_name = Some(self.types[target].id.clone());
                }
                // If the source kind is already a subtype of the target, do nothing
                if checker
                    .is_subtype(*source_kind, types, target_kind, &self.types)
                    .is_ok()
                {
                    continue;
                }

                // Otherwise, the target *must* be a subtype of the source
                // We'll remap the source below and replace
                checker
                    .is_subtype(target_kind, &self.types, *source_kind, types)
                    .with_context(|| format!("mismatched type for export `{name}`"))?;
            }

            let remapped = self.remap_extern(name, types, *source_kind, checker)?;
            if let (Some(name), ItemKind::Instance(id)) = (merged_name, remapped) {
                self.types[id].id = name;
            }
            self.types[existing].exports.insert(name.clone(), remapped);
        }

        Ok(())
    }

    fn merge_world_used_types(
        &mut self,
        existing: WorldId,
        types: &Types,
        id: WorldId,
        checker: &mut SubtypeChecker,
    ) -> Result<()> {
        let source = &types[id];
        for (name, used) in &source.uses {
            let used_interface = types[used.interface]
                .id
                .as_ref()
                .context("used type has no interface identifier")?;

            // Validate any existing used type of the same name
            if let Some(existing) = self.types[existing].uses.get(name) {
                let existing_interface = self.types[existing.interface]
                    .id
                    .as_ref()
                    .context("used type has no interface identifier")?;

                // The interface names must be on compatible semver tracks
                if !are_semver_compatible(existing_interface, used_interface) {
                    bail!("cannot merge used type `{name}` as it is expected to be from interface `{existing_interface}` but it is from interface `{used_interface}`");
                }

                // The types must be exported with the same name
                if existing.name != used.name {
                    bail!("cannot merge used type `{name}` as the export names are mismatched");
                }
            }

            // Remap the used interface; this will handle merging if we've seen the interface before
            let remapped = self.remap_interface(types, used.interface, checker)?;
            match self.types[existing].uses.get(name) {
                Some(existing) => {
                    assert_eq!(
                        existing.interface, remapped,
                        "expected a merge to have occurred"
                    );
                }
                None => {
                    let prev = self.types[existing].uses.insert(
                        name.clone(),
                        UsedType {
                            interface: remapped,
                            name: used.name.clone(),
                        },
                    );
                    assert!(prev.is_none());
                }
            }
        }

        Ok(())
    }

    fn merge_func_type(
        &mut self,
        existing: FuncTypeId,
        types: &Types,
        id: FuncTypeId,
        checker: &mut SubtypeChecker,
    ) -> Result<()> {
        // Currently function types are full equality for subtype checking, so
        // simply do a subtype check in both directions
        checker.is_subtype(
            ItemKind::Func(id),
            types,
            ItemKind::Func(existing),
            &self.types,
        )?;
        checker.is_subtype(
            ItemKind::Func(existing),
            &self.types,
            ItemKind::Func(id),
            types,
        )?;

        Ok(())
    }

    fn merge_module_type(
        &mut self,
        existing: ModuleTypeId,
        types: &Types,
        id: ModuleTypeId,
        checker: &mut SubtypeChecker,
    ) -> Result<()> {
        // Merge the module type's imports
        checker.invert();
        for (name, source_extern) in &types[id].imports {
            if let Some(target_extern) = self.types[existing].imports.get(name) {
                // If the target extern is already a subtype of the source, do nothing
                if checker
                    .core_extern(target_extern, &self.types, source_extern, types)
                    .is_ok()
                {
                    continue;
                }

                // Otherwise, the source *must* be a subtype of the target
                // We'll remap the source below and replace
                checker
                    .core_extern(source_extern, types, target_extern, &self.types)
                    .with_context(|| {
                        format!(
                            "mismatched type for import `{m}::{n}`",
                            m = name.0,
                            n = name.1
                        )
                    })?;
            }

            self.types[existing]
                .imports
                .insert(name.clone(), source_extern.clone());
        }

        checker.revert();

        // Merge the module type's exports
        for (name, source_extern) in &types[id].exports {
            if let Some(target_extern) = self.types[existing].exports.get(name) {
                // If the source kind is already a subtype of the target, do nothing
                // If the target extern is already a subtype of the source, do nothing
                if checker
                    .core_extern(source_extern, types, target_extern, &self.types)
                    .is_ok()
                {
                    continue;
                }

                // Otherwise, the target *must* be a subtype of the source
                // We'll remap the source below and replace
                checker
                    .core_extern(target_extern, &self.types, source_extern, types)
                    .with_context(|| format!("mismatched type for export `{name}`"))?;
            }

            self.types[existing]
                .exports
                .insert(name.clone(), source_extern.clone());
        }

        Ok(())
    }

    fn merge_type(
        &mut self,
        existing: Type,
        types: &Types,
        ty: Type,
        checker: &mut SubtypeChecker,
    ) -> Result<()> {
        match (existing, ty) {
            (Type::Resource(existing), Type::Resource(id)) => {
                self.merge_resource(existing, types, id, checker)
            }
            (Type::Func(existing), Type::Func(id)) => {
                self.merge_func_type(existing, types, id, checker)
            }
            (Type::Value(existing), Type::Value(ty)) => {
                self.merge_value_type(existing, types, ty, checker)
            }
            (Type::Interface(existing), Type::Interface(id)) => {
                self.merge_interface(existing, types, id, checker)
            }
            (Type::World(existing), Type::World(id)) => {
                self.merge_world(existing, types, id, checker)
            }
            (Type::Module(existing), Type::Module(id)) => {
                self.merge_module_type(existing, types, id, checker)
            }
            _ => bail!(
                "{existing} cannot be merged with {ty}",
                existing = existing.desc(&self.types),
                ty = ty.desc(types)
            ),
        }
    }

    fn merge_resource(
        &mut self,
        existing: ResourceId,
        types: &Types,
        id: ResourceId,
        checker: &mut SubtypeChecker,
    ) -> Result<()> {
        // Currently the subtype check is only checking that the underlying
        // resource names are the same; check for equality
        checker.is_subtype(
            ItemKind::Type(Type::Resource(id)),
            types,
            ItemKind::Type(Type::Resource(existing)),
            &self.types,
        )?;

        checker.is_subtype(
            ItemKind::Type(Type::Resource(existing)),
            &self.types,
            ItemKind::Type(Type::Resource(id)),
            types,
        )?;

        Ok(())
    }

    fn merge_value_type(
        &mut self,
        existing: ValueType,
        types: &Types,
        ty: ValueType,
        checker: &mut SubtypeChecker,
    ) -> Result<()> {
        // Currently the subtype check for value types is done by equality
        checker.is_subtype(
            ItemKind::Value(ty),
            types,
            ItemKind::Value(existing),
            &self.types,
        )?;

        checker.is_subtype(
            ItemKind::Value(existing),
            &self.types,
            ItemKind::Value(ty),
            types,
        )?;

        Ok(())
    }

    /// Remaps the item kind of an import or export named `name`.
    ///
    /// Each label (e.g. of an `(implements "I")` import) is an extern of its
    /// own, so a labelled instance isn't merged with other externs of its
    /// interface: its type only requires what that label's users need.
    fn remap_extern(
        &mut self,
        name: &str,
        types: &Types,
        kind: ItemKind,
        checker: &mut SubtypeChecker,
    ) -> Result<ItemKind> {
        match kind {
            ItemKind::Instance(id) if is_label(name) => Ok(ItemKind::Instance(
                self.remap_labelled_interface(types, id, checker)?,
            )),
            _ => self.remap_item_kind(types, kind, checker),
        }
    }

    fn remap_item_kind(
        &mut self,
        types: &Types,
        kind: ItemKind,
        checker: &mut SubtypeChecker,
    ) -> Result<ItemKind> {
        match kind {
            ItemKind::Type(ty) => Ok(ItemKind::Type(self.remap_type(types, ty, checker)?)),
            ItemKind::Func(id) => Ok(ItemKind::Func(self.remap_func_type(types, id, checker)?)),
            ItemKind::Instance(id) => Ok(ItemKind::Instance(
                self.remap_interface(types, id, checker)?,
            )),
            ItemKind::Component(id) => {
                Ok(ItemKind::Component(self.remap_world(types, id, checker)?))
            }
            ItemKind::Module(id) => Ok(ItemKind::Module(self.remap_module_type(types, id))),
            ItemKind::Value(ty) => Ok(ItemKind::Value(self.remap_value_type(types, ty, checker)?)),
        }
    }

    fn remap_type(
        &mut self,
        types: &Types,
        ty: Type,
        checker: &mut SubtypeChecker,
    ) -> Result<Type> {
        match ty {
            Type::Resource(id) => Ok(Type::Resource(self.remap_resource(types, id, checker)?)),
            Type::Func(id) => Ok(Type::Func(self.remap_func_type(types, id, checker)?)),
            Type::Value(ty) => Ok(Type::Value(self.remap_value_type(types, ty, checker)?)),
            Type::Interface(id) => Ok(Type::Interface(self.remap_interface(types, id, checker)?)),
            Type::World(id) => Ok(Type::World(self.remap_world(types, id, checker)?)),
            Type::Module(id) => Ok(Type::Module(self.remap_module_type(types, id))),
        }
    }

    fn remap_resource(
        &mut self,
        types: &Types,
        id: ResourceId,
        checker: &mut SubtypeChecker,
    ) -> Result<ResourceId> {
        if let Some(kind) = self.remapped.get(&Type::Resource(id)) {
            return match kind {
                Type::Resource(id) => Ok(*id),
                _ => panic!("expected a resource"),
            };
        }

        let resource = &types[id];
        let remapped = Resource {
            name: resource.name.clone(),
            alias: resource
                .alias
                .map(|a| -> Result<_> {
                    let owner = a
                        .owner
                        .map(|id| {
                            // There's no need to merge the interface here as
                            // merging is done as part of the interface remapping
                            self.remap_interface(types, id, checker)
                        })
                        .transpose()?;
                    // If there is an owning interface, ensure it is imported
                    if let Some(owner) = owner {
                        let name = self.types()[owner]
                            .id
                            .as_deref()
                            .expect("interface has no id");
                        if !self.imports.contains_key(name) {
                            self.imports
                                .insert(name.to_owned(), ItemKind::Instance(owner));
                        }
                    }
                    Ok(ResourceAlias {
                        owner,
                        source: self.remap_resource(types, a.source, checker)?,
                    })
                })
                .transpose()?,
        };
        let remapped_id = self.types.add_resource(remapped);

        let prev = self
            .remapped
            .insert(Type::Resource(id), Type::Resource(remapped_id));
        assert!(prev.is_none());
        Ok(remapped_id)
    }

    fn remap_func_type(
        &mut self,
        types: &Types,
        id: FuncTypeId,
        checker: &mut SubtypeChecker,
    ) -> Result<FuncTypeId> {
        if let Some(kind) = self.remapped.get(&Type::Func(id)) {
            return match kind {
                Type::Func(id) => Ok(*id),
                _ => panic!("expected a function type"),
            };
        }

        let ty = &types[id];
        let remapped = FuncType {
            params: ty
                .params
                .iter()
                .map(|(n, ty)| Ok((n.clone(), self.remap_value_type(types, *ty, checker)?)))
                .collect::<Result<_>>()?,
            result: ty
                .result
                .map(|ty| self.remap_value_type(types, ty, checker))
                .transpose()?,
            is_async: ty.is_async,
        };

        let remapped_id = self.types.add_func_type(remapped);
        let prev = self
            .remapped
            .insert(Type::Func(id), Type::Func(remapped_id));
        assert!(prev.is_none());
        Ok(remapped_id)
    }

    fn remap_value_type(
        &mut self,
        types: &Types,
        ty: ValueType,
        checker: &mut SubtypeChecker,
    ) -> Result<ValueType> {
        match ty {
            ValueType::Primitive(ty) => Ok(ValueType::Primitive(ty)),
            ValueType::Borrow(id) => {
                Ok(ValueType::Borrow(self.remap_resource(types, id, checker)?))
            }
            ValueType::Own(id) => Ok(ValueType::Own(self.remap_resource(types, id, checker)?)),
            ValueType::Defined(id) => Ok(ValueType::Defined(
                self.remap_defined_type(types, id, checker)?,
            )),
        }
    }

    fn remap_interface(
        &mut self,
        types: &Types,
        id: InterfaceId,
        checker: &mut SubtypeChecker,
    ) -> Result<InterfaceId> {
        // If we've seen this interface before, perform a merge
        // This will ensure that there's only a singular definition of "named" interfaces,
        // including interfaces on compatible semver tracks
        if let Some(name) = types[id].id.as_ref() {
            if let Some(existing) = self
                .interfaces
                .get(name)
                .copied()
                .or_else(|| self.find_semver_compatible_interface(name))
            {
                self.merge_interface(existing, types, id, checker)
                    .with_context(|| format!("failed to merge interface `{name}`"))?;
                // Also register this name so it can be looked up directly
                self.interfaces.insert(name.clone(), existing);
                return Ok(existing);
            }
        }

        if let Some(kind) = self.remapped.get(&Type::Interface(id)) {
            return match kind {
                Type::Interface(id) => Ok(*id),
                _ => panic!("expected an interface"),
            };
        }

        let interface = self.remap_interface_definition(types, id, checker)?;
        let remapped = self.types.add_interface(interface);
        let prev = self
            .remapped
            .insert(Type::Interface(id), Type::Interface(remapped));
        assert!(prev.is_none());

        if let Some(name) = self.types[remapped].id.as_ref() {
            let prev = self.interfaces.insert(name.clone(), remapped);
            assert!(prev.is_none());
        }

        Ok(remapped)
    }

    /// Remaps the interface of a labelled instance extern to a new interface.
    ///
    /// Unlike [`Self::remap_interface`], the new interface neither merges with
    /// other remappings of the interface nor is found by its name, as each
    /// label is an extern of its own. The types it uses or exports are
    /// remapped as usual, so they may be shared with other interfaces.
    fn remap_labelled_interface(
        &mut self,
        types: &Types,
        id: InterfaceId,
        checker: &mut SubtypeChecker,
    ) -> Result<InterfaceId> {
        let interface = self.remap_interface_definition(types, id, checker)?;
        Ok(self.types.add_interface(interface))
    }

    /// Remaps the used types and exports of an interface.
    fn remap_interface_definition(
        &mut self,
        types: &Types,
        id: InterfaceId,
        checker: &mut SubtypeChecker,
    ) -> Result<Interface> {
        let ty = &types[id];
        Ok(Interface {
            id: ty.id.clone(),
            uses: ty
                .uses
                .iter()
                .map(|(n, u)| {
                    if types[u.interface].id.is_none() {
                        bail!("used type `{n}` is from an interface without an identifier");
                    }

                    Ok((
                        n.clone(),
                        UsedType {
                            interface: self.remap_interface(types, u.interface, checker)?,
                            name: u.name.clone(),
                        },
                    ))
                })
                .collect::<Result<_>>()?,
            exports: ty
                .exports
                .iter()
                .map(|(n, k)| Ok((n.clone(), self.remap_extern(n, types, *k, checker)?)))
                .collect::<Result<_>>()?,
        })
    }

    fn remap_world(
        &mut self,
        types: &Types,
        id: WorldId,
        checker: &mut SubtypeChecker,
    ) -> Result<WorldId> {
        if let Some(kind) = self.remapped.get(&Type::World(id)) {
            return match kind {
                Type::World(id) => Ok(*id),
                _ => panic!("expected a world"),
            };
        }

        let ty = &types[id];
        let world = World {
            id: ty.id.clone(),
            uses: ty
                .uses
                .iter()
                .map(|(n, u)| {
                    if types[u.interface].id.is_none() {
                        bail!("used type `{n}` is from an interface without an identifier");
                    }

                    Ok((
                        n.clone(),
                        UsedType {
                            interface: self.remap_interface(types, u.interface, checker)?,
                            name: u.name.clone(),
                        },
                    ))
                })
                .collect::<Result<_>>()?,
            imports: ty
                .imports
                .iter()
                .map(|(n, k)| Ok((n.clone(), self.remap_extern(n, types, *k, checker)?)))
                .collect::<Result<_>>()?,
            exports: ty
                .exports
                .iter()
                .map(|(n, k)| Ok((n.clone(), self.remap_extern(n, types, *k, checker)?)))
                .collect::<Result<_>>()?,
        };

        let remapped = self.types.add_world(world);
        let prev = self.remapped.insert(Type::World(id), Type::World(remapped));
        assert!(prev.is_none());

        Ok(remapped)
    }

    fn remap_module_type(&mut self, types: &Types, id: ModuleTypeId) -> ModuleTypeId {
        if let Some(kind) = self.remapped.get(&Type::Module(id)) {
            return match kind {
                Type::Module(id) => *id,
                _ => panic!("expected a module type"),
            };
        }

        let ty = &types[id];
        let remapped = self.types.add_module_type(ty.clone());
        let prev = self
            .remapped
            .insert(Type::Module(id), Type::Module(remapped));
        assert!(prev.is_none());
        remapped
    }

    fn remap_defined_type(
        &mut self,
        types: &Types,
        id: DefinedTypeId,
        checker: &mut SubtypeChecker,
    ) -> Result<DefinedTypeId> {
        if let Some(kind) = self.remapped.get(&Type::Value(ValueType::Defined(id))) {
            return match kind {
                Type::Value(ValueType::Defined(id)) => Ok(*id),
                _ => panic!("expected a defined type got {kind:?}"),
            };
        }

        let defined = match &types[id] {
            DefinedType::Tuple(tys) => DefinedType::Tuple(
                tys.iter()
                    .map(|ty| self.remap_value_type(types, *ty, checker))
                    .collect::<Result<_>>()?,
            ),
            DefinedType::List(ty) => DefinedType::List(self.remap_value_type(types, *ty, checker)?),
            DefinedType::FixedSizeList(ty, elements) => {
                DefinedType::FixedSizeList(self.remap_value_type(types, *ty, checker)?, *elements)
            }
            DefinedType::Map(key, value) => DefinedType::Map(
                self.remap_value_type(types, *key, checker)?,
                self.remap_value_type(types, *value, checker)?,
            ),
            DefinedType::Option(ty) => {
                DefinedType::Option(self.remap_value_type(types, *ty, checker)?)
            }
            DefinedType::Result { ok, err } => DefinedType::Result {
                ok: ok
                    .as_ref()
                    .map(|ty| self.remap_value_type(types, *ty, checker))
                    .transpose()?,
                err: err
                    .as_ref()
                    .map(|ty| self.remap_value_type(types, *ty, checker))
                    .transpose()?,
            },
            DefinedType::Variant(v) => DefinedType::Variant(Variant {
                cases: v
                    .cases
                    .iter()
                    .map(|(n, ty)| {
                        Ok((
                            n.clone(),
                            ty.as_ref()
                                .map(|ty| self.remap_value_type(types, *ty, checker))
                                .transpose()?,
                        ))
                    })
                    .collect::<Result<_>>()?,
            }),
            DefinedType::Record(r) => DefinedType::Record(Record {
                fields: r
                    .fields
                    .iter()
                    .map(|(n, ty)| Ok((n.clone(), self.remap_value_type(types, *ty, checker)?)))
                    .collect::<Result<_>>()?,
            }),
            DefinedType::Flags(f) => DefinedType::Flags(f.clone()),
            DefinedType::Enum(e) => DefinedType::Enum(e.clone()),
            DefinedType::Alias(ty) => {
                DefinedType::Alias(self.remap_value_type(types, *ty, checker)?)
            }
            DefinedType::Stream(s) => DefinedType::Stream(
                s.as_ref()
                    .map(|ty| self.remap_value_type(types, *ty, checker))
                    .transpose()?,
            ),
            DefinedType::Future(f) => DefinedType::Future(
                f.as_ref()
                    .map(|ty| self.remap_value_type(types, *ty, checker))
                    .transpose()?,
            ),
        };

        let remapped = self.types.add_defined_type(defined);
        let prev = self.remapped.insert(
            Type::Value(ValueType::Defined(id)),
            Type::Value(ValueType::Defined(remapped)),
        );
        assert!(prev.is_none());
        Ok(remapped)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    // Helper to create a simple interface with optional id and exports
    fn make_interface(
        types: &mut Types,
        name: Option<&str>,
        exports: Vec<(&str, ItemKind)>,
    ) -> InterfaceId {
        let interface = Interface {
            id: name.map(|n| n.to_string()),
            uses: IndexMap::new(),
            exports: exports
                .into_iter()
                .map(|(n, k)| (n.to_string(), k))
                .collect(),
        };
        types.add_interface(interface)
    }

    // Helper to create a simple func type (no params, no result)
    fn make_func_type(types: &mut Types) -> FuncTypeId {
        types.add_func_type(FuncType {
            params: IndexMap::new(),
            result: None,
            is_async: false,
        })
    }

    #[test]
    fn semver_compatible_same_name() {
        assert!(are_semver_compatible("a:b/c@0.2.0", "a:b/c@0.2.0"));
    }

    #[test]
    fn semver_compatible_patch_versions() {
        assert!(are_semver_compatible("a:b/c@0.2.0", "a:b/c@0.2.1"));
        assert!(are_semver_compatible("a:b/c@0.2.1", "a:b/c@0.2.0"));
        assert!(are_semver_compatible("a:b/c@0.2.0", "a:b/c@0.2.3"));
    }

    #[test]
    fn semver_compatible_major_track() {
        assert!(are_semver_compatible("a:b/c@1.0.0", "a:b/c@1.1.0"));
        assert!(are_semver_compatible("a:b/c@1.0.0", "a:b/c@1.2.3"));
        assert!(are_semver_compatible("a:b/c@2.0.0", "a:b/c@2.1.0"));
    }

    #[test]
    fn semver_incompatible_minor_versions() {
        assert!(!are_semver_compatible("a:b/c@0.2.0", "a:b/c@0.3.0"));
    }

    #[test]
    fn semver_incompatible_major_versions() {
        assert!(!are_semver_compatible("a:b/c@1.0.0", "a:b/c@2.0.0"));
    }

    #[test]
    fn semver_compatible_no_version() {
        // Same name without version
        assert!(are_semver_compatible("a:b/c", "a:b/c"));
        // Different names without version
        assert!(!are_semver_compatible("a:b/c", "a:b/d"));
        // One with version, one without
        assert!(!are_semver_compatible("a:b/c@1.0.0", "a:b/c"));
        assert!(!are_semver_compatible("a:b/c", "a:b/c@1.0.0"));
    }

    #[test]
    fn semver_compatible_prerelease_rejected() {
        assert!(!are_semver_compatible("a:b/c@1.0.0-rc.1", "a:b/c@1.0.0"));
        assert!(!are_semver_compatible("a:b/c@0.2.0-pre", "a:b/c@0.2.0"));
    }

    #[test]
    fn semver_compatible_zero_patch_rejected() {
        // 0.0.x versions are not compatible with anything
        assert!(!are_semver_compatible("a:b/c@0.0.1", "a:b/c@0.0.2"));
    }

    #[test]
    fn aggregate_exact_match_merges() {
        let mut types = Types::default();
        let func_id = make_func_type(&mut types);
        let iface_id = make_interface(
            &mut types,
            Some("a:b/c@0.2.0"),
            vec![("foo", ItemKind::Func(func_id))],
        );

        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);

        let agg = TypeAggregator::new();
        let agg = agg
            .aggregate(
                "a:b/c@0.2.0",
                &types,
                ItemKind::Instance(iface_id),
                &mut checker,
            )
            .unwrap();
        // Aggregate again with the same exact name
        let agg = agg
            .aggregate(
                "a:b/c@0.2.0",
                &types,
                ItemKind::Instance(iface_id),
                &mut checker,
            )
            .unwrap();

        // Should still have one import entry (exact match merges in place)
        assert_eq!(agg.imports().count(), 1);
    }

    #[test]
    fn aggregate_semver_compatible_imports_merge() {
        let mut types1 = Types::default();
        let func_id1 = make_func_type(&mut types1);
        let iface_id1 = make_interface(
            &mut types1,
            Some("a:b/c@0.2.0"),
            vec![("foo", ItemKind::Func(func_id1))],
        );

        let mut types2 = Types::default();
        let func_id2 = make_func_type(&mut types2);
        let iface_id2 = make_interface(
            &mut types2,
            Some("a:b/c@0.2.1"),
            vec![("foo", ItemKind::Func(func_id2))],
        );

        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);

        let agg = TypeAggregator::new();
        let agg = agg
            .aggregate(
                "a:b/c@0.2.0",
                &types1,
                ItemKind::Instance(iface_id1),
                &mut checker,
            )
            .unwrap();
        let agg = agg
            .aggregate(
                "a:b/c@0.2.1",
                &types2,
                ItemKind::Instance(iface_id2),
                &mut checker,
            )
            .unwrap();

        // Only the highest version is retained in the imports
        let items: Vec<_> = agg.imports().collect();
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].0, "a:b/c@0.2.1");

        // The lower version name redirects to the canonical (highest) name
        assert_eq!(agg.canonical_import_name("a:b/c@0.2.0"), "a:b/c@0.2.1");
        assert_eq!(agg.canonical_import_name("a:b/c@0.2.1"), "a:b/c@0.2.1");
    }

    #[test]
    fn aggregate_semver_incompatible_imports_stay_separate() {
        let mut types1 = Types::default();
        let func_id1 = make_func_type(&mut types1);
        let iface_id1 = make_interface(
            &mut types1,
            Some("a:b/c@0.2.0"),
            vec![("foo", ItemKind::Func(func_id1))],
        );

        let mut types2 = Types::default();
        let func_id2 = make_func_type(&mut types2);
        let iface_id2 = make_interface(
            &mut types2,
            Some("a:b/c@0.3.0"),
            vec![("foo", ItemKind::Func(func_id2))],
        );

        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);

        let agg = TypeAggregator::new();
        let agg = agg
            .aggregate(
                "a:b/c@0.2.0",
                &types1,
                ItemKind::Instance(iface_id1),
                &mut checker,
            )
            .unwrap();
        let agg = agg
            .aggregate(
                "a:b/c@0.3.0",
                &types2,
                ItemKind::Instance(iface_id2),
                &mut checker,
            )
            .unwrap();

        // Two separate imports on different semver tracks
        let items: Vec<_> = agg.imports().collect();
        assert_eq!(items.len(), 2);
        assert_ne!(items[0].1, items[1].1);
    }

    #[test]
    fn aggregate_semver_compatible_major_merge() {
        let mut types1 = Types::default();
        let func_id1 = make_func_type(&mut types1);
        let iface_id1 = make_interface(
            &mut types1,
            Some("a:b/c@1.0.0"),
            vec![("foo", ItemKind::Func(func_id1))],
        );

        let mut types2 = Types::default();
        let func_id2 = make_func_type(&mut types2);
        let iface_id2 = make_interface(
            &mut types2,
            Some("a:b/c@1.1.0"),
            vec![("foo", ItemKind::Func(func_id2))],
        );

        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);

        let agg = TypeAggregator::new();
        let agg = agg
            .aggregate(
                "a:b/c@1.0.0",
                &types1,
                ItemKind::Instance(iface_id1),
                &mut checker,
            )
            .unwrap();
        let agg = agg
            .aggregate(
                "a:b/c@1.1.0",
                &types2,
                ItemKind::Instance(iface_id2),
                &mut checker,
            )
            .unwrap();

        // Only the highest version is retained in the imports
        let items: Vec<_> = agg.imports().collect();
        assert_eq!(items.len(), 1);
        assert_eq!(items[0].0, "a:b/c@1.1.0");

        // The lower version name redirects to the canonical (highest) name
        assert_eq!(agg.canonical_import_name("a:b/c@1.0.0"), "a:b/c@1.1.0");
        assert_eq!(agg.canonical_import_name("a:b/c@1.1.0"), "a:b/c@1.1.0");
    }

    #[test]
    fn find_compatible_import_returns_match() {
        let mut types = Types::default();
        let func_id = make_func_type(&mut types);
        let iface_id = make_interface(
            &mut types,
            Some("a:b/c@0.2.0"),
            vec![("foo", ItemKind::Func(func_id))],
        );

        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);

        let agg = TypeAggregator::new();
        let agg = agg
            .aggregate(
                "a:b/c@0.2.0",
                &types,
                ItemKind::Instance(iface_id),
                &mut checker,
            )
            .unwrap();

        assert!(agg.find_semver_compatible_import("a:b/c@0.2.1").is_some());
        assert!(agg.find_semver_compatible_import("a:b/c@0.2.5").is_some());
        assert!(agg.find_semver_compatible_import("a:b/c@0.3.0").is_none());
        assert!(agg.find_semver_compatible_import("a:b/c@1.0.0").is_none());
        assert!(agg.find_semver_compatible_import("x:y/z@0.2.0").is_none());
    }

    #[test]
    fn find_compatible_interface_returns_match() {
        let mut types = Types::default();
        let func_id = make_func_type(&mut types);
        let iface_id = make_interface(
            &mut types,
            Some("a:b/c@0.2.0"),
            vec![("foo", ItemKind::Func(func_id))],
        );

        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);

        let agg = TypeAggregator::new();
        let agg = agg
            .aggregate(
                "a:b/c@0.2.0",
                &types,
                ItemKind::Instance(iface_id),
                &mut checker,
            )
            .unwrap();

        assert!(agg
            .find_semver_compatible_interface("a:b/c@0.2.1")
            .is_some());
        assert!(agg
            .find_semver_compatible_interface("a:b/c@0.3.0")
            .is_none());
    }

    #[test]
    fn merge_used_types_from_semver_compatible_interfaces() {
        // Types1: interface "dep:pkg/types@0.2.0" used by "my:pkg/iface@1.0.0"
        let mut types1 = Types::default();
        let func1 = make_func_type(&mut types1);
        let dep_iface1 = make_interface(
            &mut types1,
            Some("dep:pkg/types@0.2.0"),
            vec![("my-func", ItemKind::Func(func1))],
        );
        let main_iface1 = {
            let mut uses = IndexMap::new();
            uses.insert(
                "my-used".to_string(),
                UsedType {
                    interface: dep_iface1,
                    name: None,
                },
            );
            let interface = Interface {
                id: Some("my:pkg/iface@1.0.0".to_string()),
                uses,
                exports: IndexMap::new(),
            };
            types1.add_interface(interface)
        };

        // Types2: interface "dep:pkg/types@0.2.1" (compatible) used by "my:pkg/iface@1.0.0"
        let mut types2 = Types::default();
        let func2 = make_func_type(&mut types2);
        let dep_iface2 = make_interface(
            &mut types2,
            Some("dep:pkg/types@0.2.1"),
            vec![("my-func", ItemKind::Func(func2))],
        );
        let main_iface2 = {
            let mut uses = IndexMap::new();
            uses.insert(
                "my-used".to_string(),
                UsedType {
                    interface: dep_iface2,
                    name: None,
                },
            );
            let interface = Interface {
                id: Some("my:pkg/iface@1.0.0".to_string()),
                uses,
                exports: IndexMap::new(),
            };
            types2.add_interface(interface)
        };

        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);

        let agg = TypeAggregator::new();
        let agg = agg
            .aggregate(
                "my:pkg/iface@1.0.0",
                &types1,
                ItemKind::Instance(main_iface1),
                &mut checker,
            )
            .unwrap();

        // This should succeed because dep:pkg/types@0.2.0 and @0.2.1 are compatible
        let _agg = agg
            .aggregate(
                "my:pkg/iface@1.0.0",
                &types2,
                ItemKind::Instance(main_iface2),
                &mut checker,
            )
            .unwrap();
    }

    #[test]
    fn merge_used_types_from_semver_incompatible_interfaces_fails() {
        // Types1: interface "dep:pkg/types@0.2.0" used by "my:pkg/iface@1.0.0"
        let mut types1 = Types::default();
        let func1 = make_func_type(&mut types1);
        let dep_iface1 = make_interface(
            &mut types1,
            Some("dep:pkg/types@0.2.0"),
            vec![("my-func", ItemKind::Func(func1))],
        );
        let main_iface1 = {
            let mut uses = IndexMap::new();
            uses.insert(
                "my-used".to_string(),
                UsedType {
                    interface: dep_iface1,
                    name: None,
                },
            );
            let interface = Interface {
                id: Some("my:pkg/iface@1.0.0".to_string()),
                uses,
                exports: IndexMap::new(),
            };
            types1.add_interface(interface)
        };

        // Types2: interface "dep:pkg/types@0.3.0" (INCOMPATIBLE) used by "my:pkg/iface@1.0.0"
        let mut types2 = Types::default();
        let func2 = make_func_type(&mut types2);
        let dep_iface2 = make_interface(
            &mut types2,
            Some("dep:pkg/types@0.3.0"),
            vec![("my-func", ItemKind::Func(func2))],
        );
        let main_iface2 = {
            let mut uses = IndexMap::new();
            uses.insert(
                "my-used".to_string(),
                UsedType {
                    interface: dep_iface2,
                    name: None,
                },
            );
            let interface = Interface {
                id: Some("my:pkg/iface@1.0.0".to_string()),
                uses,
                exports: IndexMap::new(),
            };
            types2.add_interface(interface)
        };

        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);

        let agg = TypeAggregator::new();
        let agg = agg
            .aggregate(
                "my:pkg/iface@1.0.0",
                &types1,
                ItemKind::Instance(main_iface1),
                &mut checker,
            )
            .unwrap();

        // This should fail because dep:pkg/types@0.2.0 and @0.3.0 are incompatible
        let result = agg.aggregate(
            "my:pkg/iface@1.0.0",
            &types2,
            ItemKind::Instance(main_iface2),
            &mut checker,
        );
        assert!(result.is_err());
        let err = result.unwrap_err().to_string();
        assert!(
            err.contains("cannot merge used type"),
            "unexpected error message: {err}"
        );
    }

    #[test]
    fn remap_interface_merges_semver_compatible() {
        // First aggregate an interface at @0.2.0
        let mut types1 = Types::default();
        let func_id1 = make_func_type(&mut types1);
        let iface1 = make_interface(
            &mut types1,
            Some("dep:pkg/iface@0.2.0"),
            vec![("do-thing", ItemKind::Func(func_id1))],
        );

        // Second aggregate a different interface that depends on @0.2.1 of the same
        let mut types2 = Types::default();
        let func_id2 = make_func_type(&mut types2);
        let dep_iface2 = make_interface(
            &mut types2,
            Some("dep:pkg/iface@0.2.1"),
            vec![("do-thing", ItemKind::Func(func_id2))],
        );
        let wrapper = {
            let mut exports = IndexMap::new();
            exports.insert("dep".to_string(), ItemKind::Instance(dep_iface2));
            let interface = Interface {
                id: Some("wrap:pkg/wrapper@1.0.0".to_string()),
                uses: IndexMap::new(),
                exports,
            };
            types2.add_interface(interface)
        };

        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);

        let agg = TypeAggregator::new();
        // First, aggregate the dep interface directly
        let agg = agg
            .aggregate(
                "dep:pkg/iface@0.2.0",
                &types1,
                ItemKind::Instance(iface1),
                &mut checker,
            )
            .unwrap();

        // Then aggregate a wrapper that references a compatible version.
        // The remap_interface call inside should find and merge with the existing one.
        let _agg = agg
            .aggregate(
                "wrap:pkg/wrapper@1.0.0",
                &types2,
                ItemKind::Instance(wrapper),
                &mut checker,
            )
            .unwrap();
    }

    // Helper to create a logger interface named `name` exporting a no-op func
    // for each of `funcs`
    fn make_logger(types: &mut Types, name: &str, funcs: &[&str]) -> InterfaceId {
        let exports = funcs
            .iter()
            .map(|f| (*f, ItemKind::Func(make_func_type(types))))
            .collect();
        make_interface(types, Some(name), exports)
    }

    #[test]
    fn aggregate_labels_of_one_interface_stay_separate() {
        let mut types1 = Types::default();
        let primary = make_logger(&mut types1, "a:b/logger@0.2.0", &["log"]);
        let mut types2 = Types::default();
        let backup = make_logger(&mut types2, "a:b/logger@0.2.1", &["log", "flush"]);

        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);

        let agg = TypeAggregator::new()
            .aggregate(
                "primary",
                &types1,
                ItemKind::Instance(primary),
                &mut checker,
            )
            .unwrap()
            .aggregate("backup", &types2, ItemKind::Instance(backup), &mut checker)
            .unwrap();

        // Each label keeps its own interface, version, and exports
        let imports: Vec<_> = agg
            .imports()
            .map(|(name, kind)| match kind {
                ItemKind::Instance(id) => {
                    let interface = &agg.types()[id];
                    let exports: Vec<_> = interface.exports.keys().map(String::as_str).collect();
                    (name, interface.id.as_deref().unwrap(), exports)
                }
                _ => panic!("expected an instance"),
            })
            .collect();
        assert_eq!(
            imports,
            [
                ("primary", "a:b/logger@0.2.0", vec!["log"]),
                ("backup", "a:b/logger@0.2.1", vec!["log", "flush"]),
            ]
        );
    }

    #[test]
    fn aggregate_label_keeps_highest_version() {
        let mut types1 = Types::default();
        let lower = make_logger(&mut types1, "a:b/logger@0.2.0", &["log"]);
        let mut types2 = Types::default();
        let higher = make_logger(&mut types2, "a:b/logger@0.2.1", &["log", "flush"]);

        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);

        let agg = TypeAggregator::new()
            .aggregate("primary", &types1, ItemKind::Instance(lower), &mut checker)
            .unwrap()
            .aggregate("primary", &types2, ItemKind::Instance(higher), &mut checker)
            .unwrap();

        // The label's merged interface is named after the version that
        // defines all of its exports
        let items: Vec<_> = agg.imports().collect();
        assert_eq!(items.len(), 1);
        let ItemKind::Instance(id) = items[0].1 else {
            panic!("expected an instance");
        };
        let interface = &agg.types()[id];
        assert_eq!(interface.id.as_deref(), Some("a:b/logger@0.2.1"));
        assert_eq!(
            interface.exports.keys().collect::<Vec<_>>(),
            ["log", "flush"]
        );
    }

    #[test]
    fn aggregate_label_of_incompatible_interfaces_fails() {
        let mut types1 = Types::default();
        let lower = make_logger(&mut types1, "a:b/logger@0.2.0", &["log"]);
        let mut types2 = Types::default();
        let higher = make_logger(&mut types2, "a:b/logger@0.3.0", &["log"]);

        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);

        let result = TypeAggregator::new()
            .aggregate("primary", &types1, ItemKind::Instance(lower), &mut checker)
            .unwrap()
            .aggregate("primary", &types2, ItemKind::Instance(higher), &mut checker);
        let err = result.unwrap_err().to_string();
        assert_eq!(
            err,
            "interface `a:b/logger@0.3.0` cannot be merged with interface `a:b/logger@0.2.0`"
        );
    }

    // Helper to get the interface name and export names of an instance
    fn describe(agg: &TypeAggregator, kind: ItemKind) -> (Option<&str>, Vec<&str>) {
        let ItemKind::Instance(id) = kind else {
            panic!("expected an instance");
        };
        let interface = &agg.types()[id];
        (
            interface.id.as_deref(),
            interface.exports.keys().map(String::as_str).collect(),
        )
    }

    #[test]
    fn aggregate_label_keeps_interface_name() {
        let mut types = Types::default();
        let named = make_logger(&mut types, "a:b/logger", &["log"]);
        let func = make_func_type(&mut types);
        let unnamed = make_interface(&mut types, None, vec![("log", ItemKind::Func(func))]);

        // Whichever is aggregated first, the label implements the named interface
        for order in [[unnamed, named], [named, unnamed]] {
            let mut cache = HashSet::new();
            let mut checker = SubtypeChecker::new(&mut cache);

            let agg = TypeAggregator::new()
                .aggregate(
                    "primary",
                    &types,
                    ItemKind::Instance(order[0]),
                    &mut checker,
                )
                .unwrap()
                .aggregate(
                    "primary",
                    &types,
                    ItemKind::Instance(order[1]),
                    &mut checker,
                )
                .unwrap();

            let items: Vec<_> = agg.imports().collect();
            assert_eq!(items.len(), 1);
            assert_eq!(
                describe(&agg, items[0].1),
                (Some("a:b/logger"), vec!["log"])
            );
        }
    }

    #[test]
    fn aggregate_label_in_component_import_stays_separate() {
        let mut types = Types::default();
        let label = make_logger(&mut types, "a:b/logger", &["log"]);
        let logger = make_logger(&mut types, "a:b/logger", &["log", "flush"]);
        let world = types.add_world(World {
            id: None,
            uses: IndexMap::new(),
            imports: [("primary".to_string(), ItemKind::Instance(label))]
                .into_iter()
                .collect(),
            exports: IndexMap::new(),
        });

        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);

        let agg = TypeAggregator::new()
            .aggregate("comp", &types, ItemKind::Component(world), &mut checker)
            .unwrap()
            .aggregate(
                "a:b/logger",
                &types,
                ItemKind::Instance(logger),
                &mut checker,
            )
            .unwrap();

        // The label within the component type only requires its own exports
        let imports: IndexMap<_, _> = agg.imports().collect();
        let ItemKind::Component(world) = imports["comp"] else {
            panic!("expected a component");
        };
        let label = agg.types()[world].imports["primary"];
        assert_eq!(describe(&agg, label), (Some("a:b/logger"), vec!["log"]));
        assert_eq!(
            describe(&agg, imports["a:b/logger"]),
            (Some("a:b/logger"), vec!["log", "flush"])
        );
    }

    #[test]
    fn aggregate_component_labels_check_names_even_when_shapes_match() {
        let make_world = |version: &str| {
            let mut types = Types::default();
            let logger = make_logger(&mut types, version, &["log"]);
            let world = types.add_world(World {
                id: None,
                uses: IndexMap::new(),
                imports: [("primary".to_string(), ItemKind::Instance(logger))]
                    .into_iter()
                    .collect(),
                exports: [("backup".to_string(), ItemKind::Instance(logger))]
                    .into_iter()
                    .collect(),
            });
            (types, world)
        };

        let (lower_types, lower_world) = make_world("a:b/logger@0.2.0");
        let (higher_types, higher_world) = make_world("a:b/logger@0.2.1");
        for (first_types, first_world, second_types, second_world) in [
            (&lower_types, lower_world, &higher_types, higher_world),
            (&higher_types, higher_world, &lower_types, lower_world),
        ] {
            let mut cache = HashSet::new();
            let mut checker = SubtypeChecker::new(&mut cache);
            let agg = TypeAggregator::new()
                .aggregate(
                    "comp",
                    first_types,
                    ItemKind::Component(first_world),
                    &mut checker,
                )
                .unwrap()
                .aggregate(
                    "comp",
                    second_types,
                    ItemKind::Component(second_world),
                    &mut checker,
                )
                .unwrap();
            let ItemKind::Component(world) = agg.imports().next().unwrap().1 else {
                panic!("expected a component");
            };
            for label in [
                agg.types()[world].imports["primary"],
                agg.types()[world].exports["backup"],
            ] {
                assert_eq!(describe(&agg, label).0, Some("a:b/logger@0.2.1"));
            }
        }

        let (incompatible_types, incompatible_world) = make_world("a:b/logger@0.3.0");
        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);
        let result = TypeAggregator::new()
            .aggregate(
                "comp",
                &lower_types,
                ItemKind::Component(lower_world),
                &mut checker,
            )
            .unwrap()
            .aggregate(
                "comp",
                &incompatible_types,
                ItemKind::Component(incompatible_world),
                &mut checker,
            );
        assert!(result.is_err());
    }

    #[test]
    fn aggregate_nested_labelled_exports_stay_separate() {
        let mut types = Types::default();
        let primary = make_logger(&mut types, "a:b/logger@0.2.0", &["log"]);
        let backup = make_logger(&mut types, "a:b/logger@0.2.1", &["log", "flush"]);
        let outer = make_interface(
            &mut types,
            Some("a:b/outer"),
            vec![
                ("primary", ItemKind::Instance(primary)),
                ("backup", ItemKind::Instance(backup)),
            ],
        );
        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);
        let agg = TypeAggregator::new()
            .aggregate("a:b/outer", &types, ItemKind::Instance(outer), &mut checker)
            .unwrap();
        let ItemKind::Instance(outer) = agg.imports().next().unwrap().1 else {
            panic!("expected an instance");
        };
        let exports = &agg.types()[outer].exports;
        assert_eq!(
            describe(&agg, exports["primary"]),
            (Some("a:b/logger@0.2.0"), vec!["log"])
        );
        assert_eq!(
            describe(&agg, exports["backup"]),
            (Some("a:b/logger@0.2.1"), vec!["log", "flush"])
        );
    }

    #[test]
    fn aggregate_nested_labelled_export_keeps_highest_version() {
        let make_outer = |version: &str| {
            let mut types = Types::default();
            let logger = make_logger(&mut types, version, &["log"]);
            let outer = make_interface(
                &mut types,
                Some("a:b/outer"),
                vec![("primary", ItemKind::Instance(logger))],
            );
            (types, outer)
        };
        let (lower_types, lower) = make_outer("a:b/logger@0.2.0");
        let (higher_types, higher) = make_outer("a:b/logger@0.2.1");
        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);
        let agg = TypeAggregator::new()
            .aggregate(
                "a:b/outer",
                &lower_types,
                ItemKind::Instance(lower),
                &mut checker,
            )
            .unwrap()
            .aggregate(
                "a:b/outer",
                &higher_types,
                ItemKind::Instance(higher),
                &mut checker,
            )
            .unwrap();
        let ItemKind::Instance(outer) = agg.imports().next().unwrap().1 else {
            panic!("expected an instance");
        };
        assert_eq!(
            describe(&agg, agg.types()[outer].exports["primary"]).0,
            Some("a:b/logger@0.2.1")
        );
    }

    #[test]
    fn aggregate_named_import_after_merging_nested_labels() {
        let mut types = Types::default();
        let lower = make_logger(&mut types, "a:b/logger@0.2.0", &["log"]);
        let higher = make_logger(&mut types, "a:b/logger@0.2.1", &["log", "flush"]);
        let outer_lower = make_interface(
            &mut types,
            None,
            vec![("primary", ItemKind::Instance(lower))],
        );
        let outer_higher = make_interface(
            &mut types,
            None,
            vec![("primary", ItemKind::Instance(higher))],
        );
        let mut cache = HashSet::new();
        let mut checker = SubtypeChecker::new(&mut cache);
        let agg = TypeAggregator::new()
            .aggregate(
                "outer",
                &types,
                ItemKind::Instance(outer_lower),
                &mut checker,
            )
            .unwrap()
            .aggregate(
                "outer",
                &types,
                ItemKind::Instance(outer_higher),
                &mut checker,
            )
            .unwrap()
            .aggregate(
                "a:b/logger@0.2.1",
                &types,
                ItemKind::Instance(higher),
                &mut checker,
            )
            .unwrap();

        let imports: IndexMap<_, _> = agg.imports().collect();
        // The named import must retain its full definition even though the
        // same source interface was merged into a narrower labelled export.
        assert_eq!(
            describe(&agg, imports["a:b/logger@0.2.1"]),
            (Some("a:b/logger@0.2.1"), vec!["log", "flush"])
        );
        let ItemKind::Instance(outer) = imports["outer"] else {
            panic!("expected an instance");
        };
        assert_eq!(
            describe(&agg, agg.types()[outer].exports["primary"]).1,
            vec!["log"]
        );
    }
}
