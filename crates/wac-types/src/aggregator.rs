use crate::{
    DefinedType, DefinedTypeId, FuncResult, FuncType, FuncTypeId, Interface, InterfaceId, ItemKind,
    ModuleTypeId, Record, Resource, ResourceAlias, ResourceId, SubtypeCheck, SubtypeChecker, Type,
    Types, UsedType, ValueType, Variant, World, WorldId,
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
    names: IndexMap<String, ItemKind>,
    /// A map from foreign type to remapped local type.
    remapped: HashMap<Type, Type>,
    /// A map of interface names to remapped interface id.
    interfaces: HashMap<String, InterfaceId>,
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

    /// Iterates the named types in the aggregator.
    pub fn iter(&self) -> impl Iterator<Item = (&str, ItemKind)> {
        self.names.iter().map(|(n, k)| (n.as_str(), *k))
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
        if let Some(existing) = self.names.get(name).copied() {
            self.merge_item_kind(existing, types, kind, checker)?;
            return Ok(self);
        }

        let ty = self.remap_item_kind(types, kind, checker)?;
        let prev = self.names.insert(name.to_string(), ty);
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
        // Merge the used types of the two interfaces
        self.merge_interface_used_types(existing, types, id, checker)?;

        // Merge the interface's exports
        for (name, source_kind) in &types[id].exports {
            if let Some(target_kind) = self.types[existing].exports.get(name).copied() {
                // If the source kind is already a subtype of the target, do nothing
                if checker
                    .is_subtype(
                        *source_kind,
                        types,
                        target_kind,
                        &self.types,
                        SubtypeCheck::Covariant,
                    )
                    .is_ok()
                {
                    // Keep track that the source type should be replaced with the
                    // target type wherever it's used.
                    self.remapped.insert(source_kind.ty(), target_kind.ty());
                    continue;
                }

                // Otherwise, the target *must* be a subtype of the source
                // We'll remap the source below and replace
                checker
                    .is_subtype(
                        target_kind,
                        &self.types,
                        *source_kind,
                        types,
                        SubtypeCheck::Covariant,
                    )
                    .with_context(|| format!("mismatched type for export `{name}`"))?;
            }

            let remapped = self.remap_item_kind(types, *source_kind, checker)?;
            self.types[existing].exports.insert(name.clone(), remapped);
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

                // The interface names must match
                if existing_interface != used_interface {
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
        for (name, source_kind) in &types[id].imports {
            if let Some(target_kind) = self.types[existing].imports.get(name).copied() {
                // If the target kind is already a subtype of the source, do nothing
                if checker
                    .is_subtype(
                        target_kind,
                        &self.types,
                        *source_kind,
                        types,
                        SubtypeCheck::Contravariant,
                    )
                    .is_ok()
                {
                    continue;
                }

                // Otherwise, the source *must* be a subtype of the target
                // We'll remap the source below and replace
                checker
                    .is_subtype(
                        *source_kind,
                        types,
                        target_kind,
                        &self.types,
                        SubtypeCheck::Contravariant,
                    )
                    .with_context(|| format!("mismatched type for export `{name}`"))?;
            }

            let remapped = self.remap_item_kind(types, *source_kind, checker)?;
            self.types[existing].imports.insert(name.clone(), remapped);
        }

        // Merge the worlds's exports
        for (name, source_kind) in &types[id].exports {
            if let Some(target_kind) = self.types[existing].exports.get(name).copied() {
                // If the source kind is already a subtype of the target, do nothing
                if checker
                    .is_subtype(
                        *source_kind,
                        types,
                        target_kind,
                        &self.types,
                        SubtypeCheck::Covariant,
                    )
                    .is_ok()
                {
                    continue;
                }

                // Otherwise, the target *must* be a subtype of the source
                // We'll remap the source below and replace
                checker
                    .is_subtype(
                        target_kind,
                        &self.types,
                        *source_kind,
                        types,
                        SubtypeCheck::Covariant,
                    )
                    .with_context(|| format!("mismatched type for export `{name}`"))?;
            }

            let remapped = self.remap_item_kind(types, *source_kind, checker)?;
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

                // The interface names must match
                if existing_interface != used_interface {
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
            SubtypeCheck::Covariant,
        )?;
        checker.is_subtype(
            ItemKind::Func(existing),
            &self.types,
            ItemKind::Func(id),
            types,
            SubtypeCheck::Covariant,
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
        for (name, source_extern) in &types[id].imports {
            if let Some(target_extern) = self.types[existing].imports.get(name) {
                // If the target extern is already a subtype of the source, do nothing
                checker.kinds.push(SubtypeCheck::Contravariant);
                let r = checker.core_extern(target_extern, &self.types, source_extern, types);
                checker.kinds.pop();
                if r.is_ok() {
                    continue;
                }

                // Otherwise, the source *must* be a subtype of the target
                // We'll remap the source below and replace
                checker.kinds.push(SubtypeCheck::Contravariant);
                let r = checker
                    .core_extern(source_extern, types, target_extern, &self.types)
                    .with_context(|| {
                        format!(
                            "mismatched type for import `{m}::{n}`",
                            m = name.0,
                            n = name.1
                        )
                    });
                checker.kinds.pop();
                r?;
            }

            self.types[existing]
                .imports
                .insert(name.clone(), source_extern.clone());
        }

        // Merge the module type's exports
        for (name, source_extern) in &types[id].exports {
            if let Some(target_extern) = self.types[existing].exports.get(name) {
                // If the source kind is already a subtype of the target, do nothing
                // If the target extern is already a subtype of the source, do nothing
                checker.kinds.push(SubtypeCheck::Contravariant);
                let r = checker.core_extern(source_extern, types, target_extern, &self.types);
                checker.kinds.pop();
                if r.is_ok() {
                    continue;
                }

                // Otherwise, the target *must* be a subtype of the source
                // We'll remap the source below and replace
                checker.kinds.push(SubtypeCheck::Contravariant);
                let r = checker
                    .core_extern(target_extern, &self.types, source_extern, types)
                    .with_context(|| format!("mismatched type for export `{name}`"));
                checker.kinds.pop();
                r?;
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
            SubtypeCheck::Covariant,
        )?;

        checker.is_subtype(
            ItemKind::Type(Type::Resource(existing)),
            &self.types,
            ItemKind::Type(Type::Resource(id)),
            types,
            SubtypeCheck::Covariant,
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
            SubtypeCheck::Covariant,
        )?;

        checker.is_subtype(
            ItemKind::Value(existing),
            &self.types,
            ItemKind::Value(ty),
            types,
            SubtypeCheck::Covariant,
        )?;

        Ok(())
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
                    Ok(ResourceAlias {
                        owner: a
                            .owner
                            .map(|id| self.remap_interface(types, id, checker))
                            .transpose()?,
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
            results: ty
                .results
                .as_ref()
                .map(|r| -> Result<_> {
                    match r {
                        FuncResult::Scalar(ty) => Ok(FuncResult::Scalar(
                            self.remap_value_type(types, *ty, checker)?,
                        )),
                        FuncResult::List(tys) => Ok(FuncResult::List(
                            tys.iter()
                                .map(|(n, ty)| {
                                    Ok((n.clone(), self.remap_value_type(types, *ty, checker)?))
                                })
                                .collect::<Result<_>>()?,
                        )),
                    }
                })
                .transpose()?,
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
        // This will ensure that there's only a singular definition of "named" interfaces
        if let Some(name) = types[id].id.as_ref() {
            if let Some(existing) = self.interfaces.get(name).copied() {
                self.merge_interface(existing, types, id, checker)
                    .with_context(|| format!("failed to merge interface `{name}`"))?;
                return Ok(existing);
            }
        }

        if let Some(kind) = self.remapped.get(&Type::Interface(id)) {
            return match kind {
                Type::Interface(id) => Ok(*id),
                _ => panic!("expected an interface"),
            };
        }

        let ty = &types[id];
        let interface = Interface {
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
                .map(|(n, k)| Ok((n.clone(), self.remap_item_kind(types, *k, checker)?)))
                .collect::<Result<_>>()?,
        };

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
                .map(|(n, k)| Ok((n.clone(), self.remap_item_kind(types, *k, checker)?)))
                .collect::<Result<_>>()?,
            exports: ty
                .exports
                .iter()
                .map(|(n, k)| Ok((n.clone(), self.remap_item_kind(types, *k, checker)?)))
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
