use crate::{
    DefinedType, DefinedTypeId, FuncResult, FuncType, FuncTypeId, Interface, InterfaceId, ItemKind,
    ModuleTypeId, Record, Resource, ResourceId, SubtypeCheck, SubtypeChecker, Type, Types,
    UsedType, ValueType, Variant, World, WorldId,
};
use anyhow::{bail, Context, Result};
use indexmap::IndexMap;
use std::collections::{HashMap, HashSet};

/// Used to aggregate types defined in different `Types` collections.
///
/// A type aggregator can be used to merge compatible definitions of
/// the same type into a single supertype definition stored within the
/// aggregator.
///
/// It works by first recursively remapping a type from another `Types`
/// collection into its own `Types` collection; any further attempt
/// to aggregate the type causes a merge of type definitions provided
/// they are compatible.
///
/// A type aggregator is primarily used to create types used to import
/// an implicitly-satisfied instantiation argument in a composition
/// graph; such a type must be a supertype of all referencing
/// instantiation arguments.
#[derive(Default)]
pub struct TypeAggregator {
    /// The aggregated types collection.
    types: Types,
    /// The map from name to aggregated item kind.
    names: IndexMap<String, ItemKind>,
    /// The map from original item kind to aggregated item kind.
    aggregated: HashMap<ItemKind, ItemKind>,
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
    /// aggregate type name.
    ///
    /// The provided cache is used for subtype checking.
    ///
    /// Note that if the aggregate operation fails, the aggregator is consumed.
    pub fn aggregate(
        mut self,
        name: &str,
        types: &Types,
        kind: ItemKind,
        cache: &mut HashSet<(ItemKind, ItemKind)>,
    ) -> Result<Self> {
        if let Some(existing) = self.names.get(name).copied() {
            let mut checker = SubtypeChecker::new(cache);
            self.merge_item_kind(existing, types, kind, &mut checker)?;
            return Ok(self);
        }

        let ty = self.remap_item_kind(types, kind);
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

            let remapped = self.remap_item_kind(types, *source_kind);
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
            if let Some(existing) = self.types[existing].uses.get(name) {
                if existing.name != used.name {
                    bail!("mismatched used type names");
                }

                self.merge_interface(existing.interface, types, used.interface, checker)?;
                continue;
            }

            let remapped = UsedType {
                interface: self.remap_interface(types, used.interface),
                name: used.name.clone(),
            };

            let prev = self.types[existing].uses.insert(name.clone(), remapped);
            assert!(prev.is_none());
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

            let remapped = self.remap_item_kind(types, *source_kind);
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

            let remapped = self.remap_item_kind(types, *source_kind);
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
            if let Some(existing) = self.types[existing].uses.get(name) {
                if existing.name != used.name {
                    bail!("mismatched used type names");
                }

                self.merge_interface(existing.interface, types, used.interface, checker)?;
                continue;
            }

            let remapped = UsedType {
                interface: self.remap_interface(types, used.interface),
                name: used.name.clone(),
            };

            let prev = self.types[existing].uses.insert(name.clone(), remapped);
            assert!(prev.is_none());
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
        // Currently function types perform a fully equality for subtype checking, so
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

    fn remap_item_kind(&mut self, types: &Types, kind: ItemKind) -> ItemKind {
        match kind {
            ItemKind::Type(ty) => ItemKind::Type(self.remap_type(types, ty)),
            ItemKind::Func(id) => ItemKind::Func(self.remap_func_type(types, id)),
            ItemKind::Instance(id) => ItemKind::Instance(self.remap_interface(types, id)),
            ItemKind::Component(id) => ItemKind::Component(self.remap_world(types, id)),
            ItemKind::Module(id) => ItemKind::Module(self.remap_module_type(types, id)),
            ItemKind::Value(ty) => ItemKind::Value(self.remap_value_type(types, ty)),
        }
    }

    fn remap_type(&mut self, types: &Types, ty: Type) -> Type {
        match ty {
            Type::Resource(id) => Type::Resource(self.remap_resource(types, id)),
            Type::Func(id) => Type::Func(self.remap_func_type(types, id)),
            Type::Value(ty) => Type::Value(self.remap_value_type(types, ty)),
            Type::Interface(id) => Type::Interface(self.remap_interface(types, id)),
            Type::World(id) => Type::World(self.remap_world(types, id)),
            Type::Module(id) => Type::Module(self.remap_module_type(types, id)),
        }
    }

    fn remap_resource(&mut self, types: &Types, id: ResourceId) -> ResourceId {
        if let Some(kind) = self.aggregated.get(&ItemKind::Type(Type::Resource(id))) {
            return match kind {
                ItemKind::Type(Type::Resource(id)) => *id,
                _ => panic!("expected a resource"),
            };
        }

        let resource = &types[id];
        let remapped = Resource {
            name: resource.name.clone(),
            alias_of: resource.alias_of.map(|id| self.remap_resource(types, id)),
        };
        let remapped_id = self.types.add_resource(remapped);

        let prev = self.aggregated.insert(
            ItemKind::Type(Type::Resource(id)),
            ItemKind::Type(Type::Resource(remapped_id)),
        );
        assert!(prev.is_none());
        remapped_id
    }

    fn remap_func_type(&mut self, types: &Types, id: FuncTypeId) -> FuncTypeId {
        if let Some(kind) = self.aggregated.get(&ItemKind::Type(Type::Func(id))) {
            return match kind {
                ItemKind::Type(Type::Func(id)) => *id,
                _ => panic!("expected a function type"),
            };
        }

        let ty = &types[id];
        let remapped = FuncType {
            params: ty
                .params
                .iter()
                .map(|(n, ty)| (n.clone(), self.remap_value_type(types, *ty)))
                .collect(),
            results: ty.results.as_ref().map(|r| match r {
                FuncResult::Scalar(ty) => FuncResult::Scalar(self.remap_value_type(types, *ty)),
                FuncResult::List(tys) => FuncResult::List(
                    tys.iter()
                        .map(|(n, ty)| (n.clone(), self.remap_value_type(types, *ty)))
                        .collect(),
                ),
            }),
        };

        let remapped_id = self.types.add_func_type(remapped);
        let prev = self.aggregated.insert(
            ItemKind::Type(Type::Func(id)),
            ItemKind::Type(Type::Func(remapped_id)),
        );
        assert!(prev.is_none());
        remapped_id
    }

    fn remap_value_type(&mut self, types: &Types, ty: ValueType) -> ValueType {
        match ty {
            ValueType::Primitive(ty) => ValueType::Primitive(ty),
            ValueType::Borrow(id) => ValueType::Borrow(self.remap_resource(types, id)),
            ValueType::Own(id) => ValueType::Own(self.remap_resource(types, id)),
            ValueType::Defined(id) => ValueType::Defined(self.remap_defined_type(types, id)),
        }
    }

    fn remap_interface(&mut self, types: &Types, id: InterfaceId) -> InterfaceId {
        if let Some(kind) = self.aggregated.get(&ItemKind::Type(Type::Interface(id))) {
            return match kind {
                ItemKind::Type(Type::Interface(id)) => *id,
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
                    (
                        n.clone(),
                        UsedType {
                            interface: self.remap_interface(types, u.interface),
                            name: u.name.clone(),
                        },
                    )
                })
                .collect(),
            exports: ty
                .exports
                .iter()
                .map(|(n, k)| (n.clone(), self.remap_item_kind(types, *k)))
                .collect(),
        };

        let remapped = self.types.add_interface(interface);
        let prev = self.aggregated.insert(
            ItemKind::Type(Type::Interface(id)),
            ItemKind::Type(Type::Interface(remapped)),
        );
        assert!(prev.is_none());
        remapped
    }

    fn remap_world(&mut self, types: &Types, id: WorldId) -> WorldId {
        if let Some(kind) = self.aggregated.get(&ItemKind::Type(Type::World(id))) {
            return match kind {
                ItemKind::Type(Type::World(id)) => *id,
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
                    (
                        n.clone(),
                        UsedType {
                            interface: self.remap_interface(types, u.interface),
                            name: u.name.clone(),
                        },
                    )
                })
                .collect(),
            imports: ty
                .imports
                .iter()
                .map(|(n, k)| (n.clone(), self.remap_item_kind(types, *k)))
                .collect(),
            exports: ty
                .exports
                .iter()
                .map(|(n, k)| (n.clone(), self.remap_item_kind(types, *k)))
                .collect(),
        };

        let remapped = self.types.add_world(world);
        let prev = self.aggregated.insert(
            ItemKind::Type(Type::World(id)),
            ItemKind::Type(Type::World(remapped)),
        );
        assert!(prev.is_none());
        remapped
    }

    fn remap_module_type(&mut self, types: &Types, id: ModuleTypeId) -> ModuleTypeId {
        if let Some(kind) = self.aggregated.get(&ItemKind::Type(Type::Module(id))) {
            return match kind {
                ItemKind::Type(Type::Module(id)) => *id,
                _ => panic!("expected a module type"),
            };
        }

        let ty = &types[id];
        let remapped = self.types.add_module_type(ty.clone());
        let prev = self.aggregated.insert(
            ItemKind::Type(Type::Module(id)),
            ItemKind::Type(Type::Module(remapped)),
        );
        assert!(prev.is_none());
        remapped
    }

    fn remap_defined_type(&mut self, types: &Types, id: DefinedTypeId) -> DefinedTypeId {
        if let Some(kind) = self
            .aggregated
            .get(&ItemKind::Type(Type::Value(ValueType::Defined(id))))
        {
            return match kind {
                ItemKind::Type(Type::Value(ValueType::Defined(id))) => *id,
                _ => panic!("expected a defined type got {kind:?}"),
            };
        }

        let defined = match &types[id] {
            DefinedType::Tuple(tys) => DefinedType::Tuple(
                tys.iter()
                    .map(|ty| self.remap_value_type(types, *ty))
                    .collect(),
            ),
            DefinedType::List(ty) => DefinedType::List(self.remap_value_type(types, *ty)),
            DefinedType::Option(ty) => DefinedType::Option(self.remap_value_type(types, *ty)),
            DefinedType::Result { ok, err } => DefinedType::Result {
                ok: ok.as_ref().map(|ty| self.remap_value_type(types, *ty)),
                err: err.as_ref().map(|ty| self.remap_value_type(types, *ty)),
            },
            DefinedType::Variant(v) => DefinedType::Variant(Variant {
                cases: v
                    .cases
                    .iter()
                    .map(|(n, ty)| {
                        (
                            n.clone(),
                            ty.as_ref().map(|ty| self.remap_value_type(types, *ty)),
                        )
                    })
                    .collect(),
            }),
            DefinedType::Record(r) => DefinedType::Record(Record {
                fields: r
                    .fields
                    .iter()
                    .map(|(n, ty)| (n.clone(), self.remap_value_type(types, *ty)))
                    .collect(),
            }),
            DefinedType::Flags(f) => DefinedType::Flags(f.clone()),
            DefinedType::Enum(e) => DefinedType::Enum(e.clone()),
            DefinedType::Alias(ty) => DefinedType::Alias(self.remap_value_type(types, *ty)),
        };

        let remapped = self.types.add_defined_type(defined);
        let prev = self.aggregated.insert(
            ItemKind::Type(Type::Value(ValueType::Defined(id))),
            ItemKind::Type(Type::Value(ValueType::Defined(remapped))),
        );
        assert!(prev.is_none());
        remapped
    }
}
