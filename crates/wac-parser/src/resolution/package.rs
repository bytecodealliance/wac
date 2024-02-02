use super::{
    serialize_id, CoreExtern, CoreFunc, DefinedType, Definitions, Enum, Flags, Func, FuncId,
    FuncResult, Interface, InterfaceId, ItemKind, Module, ModuleId, Record, Type, ValueType,
    Variant, World, WorldId,
};
use crate::{Resource, ResourceId, UsedType};
use anyhow::{bail, Result};
use indexmap::IndexMap;
use semver::Version;
use serde::Serialize;
use std::{collections::HashMap, fmt, rc::Rc, sync::Arc};
use wasmparser::{
    names::{ComponentName, ComponentNameKind},
    types::{self as wasm, ComponentAnyTypeId},
    Chunk, Encoding, Parser, Payload, ValidPayload, Validator, WasmFeatures,
};

/// Represents a package key that can be used in associative containers.
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PackageKey<'a> {
    /// The name of the package,
    pub name: &'a str,
    /// The version of the package.
    pub version: Option<&'a Version>,
}

impl fmt::Display for PackageKey<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{name}", name = self.name)?;
        if let Some(version) = self.version {
            write!(f, "@{version}")?;
        }
        Ok(())
    }
}

/// Represents information about a package.
///
/// A package is expected to be a valid WebAssembly component.
#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Package {
    /// The name of the package.
    pub name: String,
    /// The version of the package.
    pub version: Option<Version>,
    /// The bytes of the package.
    #[serde(skip)]
    pub bytes: Arc<Vec<u8>>,
    /// The world (component type) of the package.
    #[serde(serialize_with = "serialize_id")]
    pub world: WorldId,
    /// Defined interfaces and worlds from a WIT package.
    pub definitions: IndexMap<String, ItemKind>,
}

impl Package {
    /// Parses the given bytes into a package.
    pub(crate) fn parse(
        definitions: &mut Definitions,
        name: &str,
        version: Option<&Version>,
        bytes: Arc<Vec<u8>>,
    ) -> Result<Self> {
        if !has_magic_header(&bytes) {
            bail!("package `{name}` is expected to be a binary WebAssembly component binary but is not");
        }
        let mut parser = Parser::new(0);
        let mut parsers = Vec::new();
        let mut validator = Validator::new_with_features(WasmFeatures {
            component_model: true,
            ..Default::default()
        });
        let mut imports = Vec::new();
        let mut exports = Vec::new();

        let mut cur = bytes.as_ref().as_ref();
        loop {
            match parser.parse(cur, true)? {
                Chunk::Parsed { payload, consumed } => {
                    cur = &cur[consumed..];

                    match validator.payload(&payload)? {
                        ValidPayload::Ok => {
                            // Don't parse any sub-components or sub-modules
                            if !parsers.is_empty() {
                                continue;
                            }

                            match payload {
                                Payload::Version { encoding, .. } => {
                                    if encoding != Encoding::Component {
                                        bail!("input is not a WebAssembly component");
                                    }
                                }
                                Payload::ComponentImportSection(s) => {
                                    imports.reserve(s.count() as usize);
                                    for import in s {
                                        imports.push(import?.name.0);
                                    }
                                }
                                Payload::ComponentExportSection(s) => {
                                    exports.reserve(s.count() as usize);
                                    for export in s {
                                        exports.push(export?.name.0);
                                    }
                                }
                                _ => {}
                            }
                        }
                        ValidPayload::Func(_, _) => {}
                        ValidPayload::Parser(next) => {
                            parsers.push(parser);
                            parser = next;
                        }
                        ValidPayload::End(types) => match parsers.pop() {
                            Some(parent) => parser = parent,
                            None => {
                                let mut converter = TypeConverter::new(definitions, types);

                                let imports = imports
                                    .into_iter()
                                    .map(|i| Ok((i.to_string(), converter.import(i)?)))
                                    .collect::<Result<_>>()?;

                                let exports: IndexMap<String, ItemKind> = exports
                                    .into_iter()
                                    .map(|i| Ok((i.to_string(), converter.export(i)?)))
                                    .collect::<Result<_>>()?;

                                let world = definitions.worlds.alloc(World {
                                    id: None,
                                    uses: Default::default(),
                                    imports,
                                    exports: exports.clone(),
                                });

                                return Ok(Self {
                                    name: name.to_owned(),
                                    version: version.map(ToOwned::to_owned),
                                    bytes,
                                    world,
                                    definitions: Self::find_definitions(definitions, world),
                                });
                            }
                        },
                    }
                }
                Chunk::NeedMoreData(_) => unreachable!(),
            }
        }
    }

    fn find_definitions(definitions: &Definitions, world: WorldId) -> IndexMap<String, ItemKind> {
        // Look for any component type exports that export a component type or instance type
        let exports = &definitions.worlds[world].exports;
        let mut defs = IndexMap::new();
        for (name, kind) in exports {
            if let ItemKind::Type(Type::World(id)) = kind {
                let world = &definitions.worlds[*id];
                if world.exports.len() != 1 {
                    continue;
                }

                // Check if the export name is an interface name
                let (export_name, kind) = world.exports.get_index(0).unwrap();
                match ComponentName::new(export_name, 0).unwrap().kind() {
                    ComponentNameKind::Interface(_) => {}
                    _ => continue,
                }

                match kind {
                    ItemKind::Instance(id) => {
                        defs.insert(name.clone(), ItemKind::Type(Type::Interface(*id)));
                    }
                    ItemKind::Component(id) => {
                        defs.insert(name.clone(), ItemKind::Type(Type::World(*id)));
                    }
                    _ => continue,
                }
            }
        }

        defs
    }
}

/// Whether the given bytes have a magic header indicating a WebAssembly binary.
fn has_magic_header(bytes: &[u8]) -> bool {
    bytes.starts_with(b"\0asm")
}

impl fmt::Debug for Package {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Package")
            .field("name", &self.name)
            .field("version", &self.version)
            .field("bytes", &"...")
            .field("world", &self.world)
            .field("definitions", &self.definitions)
            .finish()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Owner {
    /// The owner is an interface.
    Interface(InterfaceId),
    /// The owner is a world.
    World(WorldId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Entity {
    /// The entity is a type.
    Type(Type),
    /// The entity is a resource.
    Resource(ResourceId),
}

/// Responsible for converting between wasmparser and wac-parser type
/// representations.
struct TypeConverter<'a> {
    definitions: &'a mut Definitions,
    types: Rc<wasm::Types>,
    cache: HashMap<wasm::AnyTypeId, Entity>,
    resource_map: HashMap<wasm::ResourceId, ResourceId>,
    owners: HashMap<wasm::ComponentAnyTypeId, (Owner, String)>,
}

impl<'a> TypeConverter<'a> {
    fn new(definitions: &'a mut Definitions, types: wasm::Types) -> Self {
        let types = Rc::new(types);
        Self {
            definitions,
            types,
            cache: Default::default(),
            resource_map: Default::default(),
            owners: Default::default(),
        }
    }

    fn import(&mut self, name: &str) -> Result<ItemKind> {
        let import = self.types.component_entity_type_of_import(name).unwrap();
        self.entity(name, import)
    }

    fn export(&mut self, name: &str) -> Result<ItemKind> {
        let export = self.types.component_entity_type_of_export(name).unwrap();
        self.entity(name, export)
    }

    fn component_func_type(&mut self, id: wasm::ComponentFuncTypeId) -> Result<FuncId> {
        let key = wasm::AnyTypeId::Component(wasm::ComponentAnyTypeId::Func(id));
        if let Some(ty) = self.cache.get(&key) {
            match ty {
                Entity::Type(Type::Func(id)) => return Ok(*id),
                _ => unreachable!("invalid cached type"),
            }
        }

        let types = self.types.clone();
        let func_ty = &types[id];
        let params = func_ty
            .params
            .iter()
            .map(|(name, ty)| Ok((name.to_string(), self.component_val_type(*ty)?)))
            .collect::<Result<_>>()?;

        let results = if func_ty.results.len() == 0 {
            None
        } else if func_ty.results.len() == 1 && func_ty.results[0].0.is_none() {
            Some(FuncResult::Scalar(
                self.component_val_type(func_ty.results[0].1)?,
            ))
        } else {
            Some(FuncResult::List(
                func_ty
                    .results
                    .iter()
                    .map(|(name, ty)| {
                        Ok((
                            name.as_ref().unwrap().to_string(),
                            self.component_val_type(*ty)?,
                        ))
                    })
                    .collect::<Result<_>>()?,
            ))
        };

        let id = self.definitions.funcs.alloc(Func { params, results });
        self.cache.insert(key, Entity::Type(Type::Func(id)));
        Ok(id)
    }

    fn module_type(&mut self, id: wasm::ComponentCoreModuleTypeId) -> Result<ModuleId> {
        let key = wasm::AnyTypeId::Core(wasm::ComponentCoreTypeId::Module(id));
        if let Some(ty) = self.cache.get(&key) {
            match ty {
                Entity::Type(Type::Module(id)) => return Ok(*id),
                _ => unreachable!("invalid cached type"),
            }
        }

        let module_ty = &self.types[id];

        let imports = module_ty
            .imports
            .iter()
            .map(|((module, name), ty)| ((module.clone(), name.clone()), self.entity_type(*ty)))
            .collect();

        let exports = module_ty
            .exports
            .iter()
            .map(|(name, ty)| (name.clone(), self.entity_type(*ty)))
            .collect();

        let module_id = self.definitions.modules.alloc(Module { imports, exports });
        self.cache
            .insert(key, Entity::Type(Type::Module(module_id)));
        Ok(module_id)
    }

    fn ty(&mut self, id: wasm::ComponentAnyTypeId) -> Result<Type> {
        match id {
            wasm::ComponentAnyTypeId::Defined(id) => {
                Ok(Type::Value(self.component_defined_type(id)?))
            }
            wasm::ComponentAnyTypeId::Func(id) => Ok(Type::Func(self.component_func_type(id)?)),
            wasm::ComponentAnyTypeId::Component(id) => {
                Ok(Type::World(self.component_type(None, id)?))
            }
            wasm::ComponentAnyTypeId::Instance(id) => {
                Ok(Type::Interface(self.component_instance_type(None, id)?))
            }
            wasm::ComponentAnyTypeId::Resource(_) => {
                bail!("unexpected resource encountered")
            }
        }
    }

    fn component_val_type(&mut self, ty: wasm::ComponentValType) -> Result<ValueType> {
        match ty {
            wasm::ComponentValType::Primitive(ty) => Ok(ValueType::Primitive(ty.into())),
            wasm::ComponentValType::Type(id) => Ok(self.component_defined_type(id)?),
        }
    }

    fn component_instance_type(
        &mut self,
        name: Option<&str>,
        id: wasm::ComponentInstanceTypeId,
    ) -> Result<InterfaceId> {
        let key = wasm::AnyTypeId::Component(wasm::ComponentAnyTypeId::Instance(id));
        if let Some(ty) = self.cache.get(&key) {
            match ty {
                Entity::Type(Type::Interface(id)) => {
                    return Ok(*id);
                }
                _ => unreachable!("invalid cached type"),
            }
        }

        let types = self.types.clone();
        let instance_ty = &types[id];
        let id = self.definitions.interfaces.alloc(Interface {
            id: name.and_then(|n| n.contains(':').then(|| n.to_owned())),
            remapped_types: Default::default(),
            uses: Default::default(),
            exports: IndexMap::with_capacity(instance_ty.exports.len()),
        });

        for (name, ty) in &instance_ty.exports {
            let export = self.entity(name, *ty)?;

            if let wasm::ComponentEntityType::Type {
                referenced,
                created,
            } = ty
            {
                self.use_or_own(Owner::Interface(id), name, *referenced, *created);
            }

            let prev = self.definitions.interfaces[id]
                .exports
                .insert(name.clone(), export);
            assert!(prev.is_none());
        }

        self.cache.insert(key, Entity::Type(Type::Interface(id)));
        Ok(id)
    }

    fn entity(&mut self, name: &str, ty: wasm::ComponentEntityType) -> Result<ItemKind> {
        match ty {
            wasm::ComponentEntityType::Module(id) => Ok(ItemKind::Module(self.module_type(id)?)),
            wasm::ComponentEntityType::Value(ty) => {
                Ok(ItemKind::Value(self.component_val_type(ty)?))
            }
            wasm::ComponentEntityType::Type {
                created: wasm::ComponentAnyTypeId::Resource(id),
                ..
            } => Ok(ItemKind::Resource(self.resource(name, id))),
            wasm::ComponentEntityType::Type { created, .. } => {
                Ok(ItemKind::Type(self.ty(created)?))
            }
            wasm::ComponentEntityType::Func(id) => {
                Ok(ItemKind::Func(self.component_func_type(id)?))
            }
            wasm::ComponentEntityType::Instance(id) => Ok(ItemKind::Instance(
                self.component_instance_type(Some(name), id)?,
            )),
            wasm::ComponentEntityType::Component(id) => {
                Ok(ItemKind::Component(self.component_type(Some(name), id)?))
            }
        }
    }

    fn use_or_own(
        &mut self,
        owner: Owner,
        name: &str,
        referenced: ComponentAnyTypeId,
        created: ComponentAnyTypeId,
    ) {
        if let Some((other, orig)) = self.find_owner(referenced) {
            match *other {
                Owner::Interface(interface) if owner != *other => {
                    let used = UsedType {
                        interface,
                        name: if name != orig {
                            Some(orig.to_string())
                        } else {
                            None
                        },
                    };

                    // Owner is a different interface, so add a using reference
                    let uses = match owner {
                        Owner::Interface(id) => &mut self.definitions.interfaces[id].uses,
                        Owner::World(id) => &mut self.definitions.worlds[id].uses,
                    };

                    uses.insert(name.to_string(), used);
                }
                _ => {}
            }
            return;
        }

        // Take ownership of the entity
        let prev = self.owners.insert(created, (owner, name.to_string()));
        assert!(prev.is_none());
    }

    fn component_type(&mut self, name: Option<&str>, id: wasm::ComponentTypeId) -> Result<WorldId> {
        let key = wasm::AnyTypeId::Component(wasm::ComponentAnyTypeId::Component(id));
        if let Some(ty) = self.cache.get(&key) {
            match ty {
                Entity::Type(Type::World(id)) => return Ok(*id),
                _ => unreachable!("invalid cached type"),
            }
        }

        let types = self.types.clone();
        let component_ty = &types[id];
        let id = self.definitions.worlds.alloc(World {
            id: name.and_then(|n| n.contains(':').then(|| n.to_owned())),
            uses: Default::default(),
            imports: IndexMap::with_capacity(component_ty.imports.len()),
            exports: IndexMap::with_capacity(component_ty.exports.len()),
        });

        for (name, ty) in &component_ty.imports {
            let import = self.entity(name, *ty)?;

            if let wasm::ComponentEntityType::Type {
                referenced,
                created,
            } = ty
            {
                self.use_or_own(Owner::World(id), name, *referenced, *created);
            }

            let prev = self.definitions.worlds[id]
                .imports
                .insert(name.clone(), import);
            assert!(prev.is_none());
        }

        for (name, ty) in &component_ty.exports {
            let ty = self.entity(name, *ty)?;
            let prev = self.definitions.worlds[id].exports.insert(name.clone(), ty);
            assert!(prev.is_none());
        }

        self.cache.insert(key, Entity::Type(Type::World(id)));
        Ok(id)
    }

    fn component_defined_type(&mut self, id: wasm::ComponentDefinedTypeId) -> Result<ValueType> {
        let key = wasm::AnyTypeId::Component(wasm::ComponentAnyTypeId::Defined(id));
        if let Some(ty) = self.cache.get(&key) {
            match ty {
                Entity::Type(Type::Value(ty)) => return Ok(*ty),
                _ => unreachable!("invalid cached type"),
            }
        }

        let types = self.types.clone();
        let ty = match &types[id] {
            wasm::ComponentDefinedType::Primitive(ty) => ValueType::Defined {
                id: self
                    .definitions
                    .types
                    .alloc(DefinedType::Alias(ValueType::Primitive((*ty).into()))),
                contains_borrow: false,
            },
            wasm::ComponentDefinedType::Record(ty) => {
                let mut contains_borrow = false;
                let fields = ty
                    .fields
                    .iter()
                    .map(|(name, ty)| {
                        let ty = self.component_val_type(*ty)?;
                        contains_borrow |= ty.contains_borrow();
                        Ok((name.as_str().to_owned(), ty))
                    })
                    .collect::<Result<_>>()?;

                ValueType::Defined {
                    id: self
                        .definitions
                        .types
                        .alloc(DefinedType::Record(Record { fields })),
                    contains_borrow,
                }
            }
            wasm::ComponentDefinedType::Variant(ty) => {
                let mut contains_borrow = false;
                let cases = ty
                    .cases
                    .iter()
                    .map(|(name, case)| {
                        let ty = case.ty.map(|ty| self.component_val_type(ty)).transpose()?;
                        contains_borrow |= ty.as_ref().map_or(false, ValueType::contains_borrow);
                        Ok((name.as_str().to_owned(), ty))
                    })
                    .collect::<Result<_>>()?;

                ValueType::Defined {
                    id: self
                        .definitions
                        .types
                        .alloc(DefinedType::Variant(Variant { cases })),
                    contains_borrow,
                }
            }
            wasm::ComponentDefinedType::List(ty) => {
                let ty = self.component_val_type(*ty)?;
                ValueType::Defined {
                    id: self.definitions.types.alloc(DefinedType::List(ty)),
                    contains_borrow: ty.contains_borrow(),
                }
            }
            wasm::ComponentDefinedType::Tuple(ty) => {
                let mut contains_borrow = false;
                let types = ty
                    .types
                    .iter()
                    .map(|ty| {
                        let ty = self.component_val_type(*ty)?;
                        contains_borrow |= ty.contains_borrow();
                        Ok(ty)
                    })
                    .collect::<Result<_>>()?;
                ValueType::Defined {
                    id: self.definitions.types.alloc(DefinedType::Tuple(types)),
                    contains_borrow,
                }
            }
            wasm::ComponentDefinedType::Flags(flags) => {
                let flags = flags.iter().map(|flag| flag.as_str().to_owned()).collect();
                ValueType::Defined {
                    id: self
                        .definitions
                        .types
                        .alloc(DefinedType::Flags(Flags(flags))),
                    contains_borrow: false,
                }
            }
            wasm::ComponentDefinedType::Enum(cases) => {
                let cases = cases.iter().map(|case| case.as_str().to_owned()).collect();
                ValueType::Defined {
                    id: self.definitions.types.alloc(DefinedType::Enum(Enum(cases))),
                    contains_borrow: false,
                }
            }
            wasm::ComponentDefinedType::Option(ty) => {
                let ty = self.component_val_type(*ty)?;
                ValueType::Defined {
                    id: self.definitions.types.alloc(DefinedType::Option(ty)),
                    contains_borrow: ty.contains_borrow(),
                }
            }
            wasm::ComponentDefinedType::Result { ok, err } => {
                let ok = ok.map(|ty| self.component_val_type(ty)).transpose()?;
                let err = err.map(|ty| self.component_val_type(ty)).transpose()?;
                ValueType::Defined {
                    id: self
                        .definitions
                        .types
                        .alloc(DefinedType::Result { ok, err }),
                    contains_borrow: ok.as_ref().map_or(false, ValueType::contains_borrow)
                        || err.as_ref().map_or(false, ValueType::contains_borrow),
                }
            }
            wasm::ComponentDefinedType::Borrow(id) => ValueType::Borrow(
                match self.cache.get(&wasm::AnyTypeId::Component(
                    wasm::ComponentAnyTypeId::Resource(*id),
                )) {
                    Some(Entity::Resource(id)) => *id,
                    _ => unreachable!("expected a resource"),
                },
            ),
            wasm::ComponentDefinedType::Own(id) => ValueType::Own(
                match self.cache.get(&wasm::AnyTypeId::Component(
                    wasm::ComponentAnyTypeId::Resource(*id),
                )) {
                    Some(Entity::Resource(id)) => *id,
                    _ => unreachable!("expected a resource"),
                },
            ),
        };

        self.cache.insert(key, Entity::Type(Type::Value(ty)));
        Ok(ty)
    }

    fn resource(&mut self, name: &str, id: wasm::AliasableResourceId) -> ResourceId {
        let key = wasm::AnyTypeId::Component(wasm::ComponentAnyTypeId::Resource(id));
        if let Some(ty) = self.cache.get(&key) {
            match ty {
                Entity::Resource(id) => return *id,
                _ => unreachable!("invalid cached type"),
            }
        }

        // Check if this is an alias of another resource
        if let Some(resource_id) = self.resource_map.get(&id.resource()) {
            let alias_id = self.definitions.resources.alloc(Resource {
                name: name.to_owned(),
                alias_of: Some(*resource_id),
            });
            self.cache.insert(key, Entity::Resource(alias_id));
            return alias_id;
        }

        // Otherwise, this is a new resource
        let resource_id = self.definitions.resources.alloc(Resource {
            name: name.to_owned(),
            alias_of: None,
        });

        self.resource_map.insert(id.resource(), resource_id);
        self.cache.insert(key, Entity::Resource(resource_id));
        resource_id
    }

    fn entity_type(&self, ty: wasm::EntityType) -> CoreExtern {
        match ty {
            wasm::EntityType::Func(ty) => CoreExtern::Func(self.func_type(ty)),
            wasm::EntityType::Table(ty) => ty.into(),
            wasm::EntityType::Memory(ty) => ty.into(),
            wasm::EntityType::Global(ty) => ty.into(),
            wasm::EntityType::Tag(ty) => CoreExtern::Tag(self.func_type(ty)),
        }
    }

    fn func_type(&self, ty: wasm::CoreTypeId) -> CoreFunc {
        let func_ty = self.types[ty].unwrap_func();
        CoreFunc {
            params: func_ty.params().iter().copied().map(Into::into).collect(),
            results: func_ty.results().iter().copied().map(Into::into).collect(),
        }
    }

    fn find_owner(&self, mut id: wasm::ComponentAnyTypeId) -> Option<&(Owner, String)> {
        let mut prev = None;
        while prev.is_none() {
            prev = self.owners.get(&id);
            id = match self.types.peel_alias(id) {
                Some(next) => next,
                None => break,
            };
        }
        prev
    }
}
