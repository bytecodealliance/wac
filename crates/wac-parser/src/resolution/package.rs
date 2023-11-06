use self::cache::{MappedResourceId, ResourceMapper, TypeCache};
use super::{
    CoreExtern, CoreFunc, DefinedType, DefinedTypeId, Definitions, Enum, Extern, Flags, Func,
    FuncId, FuncKind, FuncResult, Interface, InterfaceId, ItemKind, Module, ModuleId, Record,
    Resource, ResourceMethod, Type, ValueType, Variant, World, WorldId,
};
use anyhow::{bail, Result};
use indexmap::IndexMap;
use std::{collections::HashMap, fmt, rc::Rc};
use wasmparser::{
    types::{self as wasm},
    Chunk, Encoding, Parser, Payload, ValidPayload, Validator, WasmFeatures,
};

mod cache;

/// Represents information about a package.
///
/// A package is expected to be a valid WebAssembly component.
pub struct Package {
    /// The bytes of the package.
    pub bytes: Vec<u8>,
    /// The world (component type) of the package.
    pub ty: WorldId,
    /// Defined interfaces and worlds from a WIT package.
    pub definitions: HashMap<String, ItemKind>,
}

impl Package {
    /// Parses the given bytes into a package.
    pub(crate) fn parse(definitions: &mut Definitions, bytes: Vec<u8>) -> Result<Self> {
        let mut parser = Parser::new(0);
        let mut parsers = Vec::new();
        let mut validator = Validator::new_with_features(WasmFeatures {
            component_model: true,
            ..Default::default()
        });
        let mut imports = Vec::new();
        let mut exports = Vec::new();

        let mut cur = bytes.as_ref();
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

                                let exports = exports
                                    .into_iter()
                                    .map(|i| Ok((i.to_string(), converter.export(i)?)))
                                    .collect::<Result<_>>()?;

                                let ty = definitions.worlds.alloc(World {
                                    imports,
                                    exports,
                                    scope: None,
                                });

                                return Ok(Self {
                                    bytes,
                                    ty,
                                    definitions: Self::find_definitions(definitions, ty),
                                });
                            }
                        },
                    }
                }
                Chunk::NeedMoreData(_) => unreachable!(),
            }
        }
    }

    fn find_definitions(definitions: &Definitions, world: WorldId) -> HashMap<String, ItemKind> {
        // Look for any component type exports that export a component type or instance type
        let exports = &definitions.worlds[world].exports;
        let mut defs = HashMap::new();
        for (name, ext) in exports {
            if let Extern::Kind(ItemKind::Type(Type::World(id))) = ext {
                let world = &definitions.worlds[*id];
                if world.exports.len() != 1 {
                    continue;
                }

                // Check if the export name is fully qualified
                let (qname, ext) = world.exports.get_index(0).unwrap();
                if !qname.contains(':') {
                    continue;
                }

                match ext.kind() {
                    ItemKind::Instance(id) => {
                        defs.insert(name.clone(), ItemKind::Type(Type::Interface(id)));
                    }
                    ItemKind::Component(id) => {
                        defs.insert(name.clone(), ItemKind::Type(Type::World(id)));
                    }
                    _ => continue,
                }
            }
        }

        defs
    }
}

impl fmt::Debug for Package {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Package")
            .field("bytes", &"...")
            .field("ty", &self.ty)
            .field("definitions", &self.definitions)
            .finish()
    }
}

/// Responsible for converting between wasmparser and wac-parser type
/// representations.
struct TypeConverter<'a> {
    definitions: &'a mut Definitions,
    types: Rc<wasm::Types>,
    cache: TypeCache,
    mapper: ResourceMapper,
    owners: HashMap<wasm::AnyTypeId, (InterfaceId, usize)>,
    resources: HashMap<MappedResourceId, DefinedTypeId>,
}

impl<'a> TypeConverter<'a> {
    fn new(definitions: &'a mut Definitions, types: wasm::Types) -> Self {
        let types = Rc::new(types);
        let mapper = ResourceMapper::new(types.clone());
        let cache = TypeCache::new(types.clone(), mapper.map());
        Self {
            definitions,
            types,
            cache,
            mapper,
            owners: Default::default(),
            resources: Default::default(),
        }
    }

    fn import(&mut self, name: &str) -> Result<Extern> {
        let import = self.types.component_entity_type_of_import(name).unwrap();
        // We must map any resources before we can convert the import
        self.mapper.component_entity_type(name, import);
        Ok(Extern::Kind(self.component_entity_type(name, import)?))
    }

    fn export(&mut self, name: &str) -> Result<Extern> {
        let export = self.types.component_entity_type_of_export(name).unwrap();
        // We must map any resources before we can convert the export
        self.mapper.component_entity_type(name, export);
        Ok(Extern::Kind(self.component_entity_type(name, export)?))
    }

    fn component_entity_type(
        &mut self,
        name: &str,
        ty: wasm::ComponentEntityType,
    ) -> Result<ItemKind> {
        match ty {
            wasm::ComponentEntityType::Module(id) => Ok(ItemKind::Module(self.module_type(id)?)),
            wasm::ComponentEntityType::Func(id) => Ok(ItemKind::Func(
                self.component_func_type(id, FuncKind::Free)?,
            )),
            wasm::ComponentEntityType::Value(ty) => {
                Ok(ItemKind::Value(self.component_val_type(ty)?))
            }
            wasm::ComponentEntityType::Type { referenced, .. } => Ok(ItemKind::Type(
                self.ty(wasm::AnyTypeId::Component(referenced))?,
            )),
            wasm::ComponentEntityType::Instance(ty) => Ok(ItemKind::Instance(
                self.component_instance_type(Some(name), ty)?,
            )),
            wasm::ComponentEntityType::Component(ty) => {
                Ok(ItemKind::Component(self.component_type(ty)?))
            }
        }
    }

    fn component_func_type(
        &mut self,
        id: wasm::ComponentFuncTypeId,
        kind: FuncKind,
    ) -> Result<FuncId> {
        let key = self.cache.key(
            None,
            wasm::AnyTypeId::Component(wasm::ComponentAnyTypeId::Func(id)),
        );
        if let Some(ty) = self.cache.get(&key) {
            match ty {
                Type::Func(id) => return Ok(id),
                _ => unreachable!("invalid cached type"),
            }
        }

        let types = self.types.clone();
        let func_ty = &types[id];
        let params = func_ty
            .params
            .iter()
            .skip(if kind == FuncKind::Method { 1 } else { 0 })
            .map(|(name, ty)| Ok((name.to_string(), self.component_val_type(*ty)?)))
            .collect::<Result<_>>()?;

        let results = if kind == FuncKind::Constructor || func_ty.results.len() == 0 {
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
        self.cache.insert(key, Type::Func(id));
        Ok(id)
    }

    fn module_type(&mut self, id: wasm::ComponentCoreModuleTypeId) -> Result<ModuleId> {
        let key = self.cache.key(
            None,
            wasm::AnyTypeId::Core(wasm::ComponentCoreTypeId::Module(id)),
        );
        if let Some(ty) = self.cache.get(&key) {
            match ty {
                Type::Module(id) => return Ok(id),
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

        let id = self.definitions.modules.alloc(Module { imports, exports });

        self.cache.insert(key, Type::Module(id));
        Ok(id)
    }

    fn ty(&mut self, id: wasm::AnyTypeId) -> Result<Type> {
        match id {
            wasm::AnyTypeId::Component(wasm::ComponentAnyTypeId::Defined(id)) => {
                Ok(Type::Value(self.component_defined_type(id)?))
            }
            wasm::AnyTypeId::Component(wasm::ComponentAnyTypeId::Resource(id)) => {
                Ok(Type::Value(self.resource(id)))
            }
            wasm::AnyTypeId::Component(wasm::ComponentAnyTypeId::Func(id)) => {
                Ok(Type::Func(self.component_func_type(id, FuncKind::Free)?))
            }
            wasm::AnyTypeId::Core(wasm::ComponentCoreTypeId::Module(id)) => {
                Ok(Type::Module(self.module_type(id)?))
            }
            wasm::AnyTypeId::Component(wasm::ComponentAnyTypeId::Component(id)) => {
                Ok(Type::World(self.component_type(id)?))
            }
            wasm::AnyTypeId::Component(wasm::ComponentAnyTypeId::Instance(id)) => {
                Ok(Type::Interface(self.component_instance_type(None, id)?))
            }
            wasm::AnyTypeId::Core(wasm::ComponentCoreTypeId::Sub(_)) => {
                unreachable!("not a valid component extern type")
            }
        }
    }

    fn component_val_type(&mut self, ty: wasm::ComponentValType) -> Result<ValueType> {
        match ty {
            wasm::ComponentValType::Primitive(ty) => Ok(ValueType::Primitive(ty.into())),
            wasm::ComponentValType::Type(id) => {
                Ok(ValueType::Defined(self.component_defined_type(id)?))
            }
        }
    }

    fn component_instance_type(
        &mut self,
        name: Option<&str>,
        id: wasm::ComponentInstanceTypeId,
    ) -> Result<InterfaceId> {
        let key = self.cache.key(
            name,
            wasm::AnyTypeId::Component(wasm::ComponentAnyTypeId::Instance(id)),
        );
        if let Some(cached_ty) = self.cache.get(&key) {
            match cached_ty {
                Type::Interface(iface_id) => {
                    // We still need to map ownership of any types for this interface
                    for (index, (_, ty)) in self.types[id].exports.iter().enumerate() {
                        if let wasm::ComponentEntityType::Type { referenced, .. } = ty {
                            let ty = self.resolve_alias(*referenced);
                            self.owners.insert(ty, (iface_id, index));
                        }
                    }

                    return Ok(iface_id);
                }
                _ => unreachable!("invalid cached type"),
            }
        }

        let types = self.types.clone();
        let instance_ty = &types[id];

        let id = self.definitions.interfaces.alloc(Interface {
            id: name.and_then(|n| n.contains(':').then(|| n.to_owned())),
            exports: IndexMap::with_capacity(instance_ty.exports.len()),
            scope: None,
        });

        for (index, (name, ty)) in instance_ty.exports.iter().enumerate() {
            let export = match ty {
                wasm::ComponentEntityType::Type { referenced, .. } => {
                    let ty = self.resolve_alias(*referenced);
                    let converted_ty = self.ty(ty)?;
                    let (interface, index) = *self.owners.entry(ty).or_insert((id, index));

                    match converted_ty {
                        Type::Value(ty) if interface != id => Extern::Use {
                            interface,
                            export_index: index,
                            ty,
                        },
                        _ => Extern::Kind(ItemKind::Type(converted_ty)),
                    }
                }
                wasm::ComponentEntityType::Func(ty) => {
                    match self.resource_method_or_func(&instance_ty.exports, name, *ty)? {
                        Some(export) => export,
                        None => continue,
                    }
                }
                _ => Extern::Kind(self.component_entity_type(name, *ty)?),
            };

            let prev = self.definitions.interfaces[id]
                .exports
                .insert(name.clone(), export);
            assert!(prev.is_none());
        }

        self.cache.insert(key, Type::Interface(id));
        Ok(id)
    }

    fn resource_export(
        &mut self,
        externs: &IndexMap<String, wasm::ComponentEntityType>,
        name: &str,
    ) -> &mut Resource {
        match externs[name] {
            wasm::ComponentEntityType::Type {
                referenced: wasm::ComponentAnyTypeId::Resource(id),
                ..
            } => {
                let id = self
                    .mapper
                    .get(id.resource())
                    .expect("resource should be mapped");
                let id = self.resources[&id];
                match self.definitions.types[id] {
                    DefinedType::Resource(id) => &mut self.definitions.resources[id],
                    _ => unreachable!("expected type to be a resource type"),
                }
            }
            _ => unreachable!("expected a type export"),
        }
    }

    fn resource_method_or_func(
        &mut self,
        externs: &IndexMap<String, wasm::ComponentEntityType>,
        name: &str,
        id: wasm::ComponentFuncTypeId,
    ) -> Result<Option<Extern>> {
        if let Some(res) = name.strip_prefix("[constructor]") {
            let id = self.component_func_type(id, FuncKind::Constructor)?;
            self.resource_export(externs, res).methods.insert(
                String::new(),
                ResourceMethod {
                    kind: FuncKind::Constructor,
                    ty: id,
                },
            );
            Ok(None)
        } else if let Some(name) = name.strip_prefix("[method]") {
            let (res, name) = name.split_once('.').unwrap();
            let id = self.component_func_type(id, FuncKind::Method)?;
            self.resource_export(externs, res).methods.insert(
                name.to_owned(),
                ResourceMethod {
                    kind: FuncKind::Method,
                    ty: id,
                },
            );
            Ok(None)
        } else if let Some(name) = name.strip_prefix("[static]") {
            let (res, name) = name.split_once('.').unwrap();
            let id = self.component_func_type(id, FuncKind::Static)?;
            self.resource_export(externs, res).methods.insert(
                name.to_owned(),
                ResourceMethod {
                    kind: FuncKind::Static,
                    ty: id,
                },
            );
            Ok(None)
        } else {
            Ok(Some(Extern::Kind(ItemKind::Func(
                self.component_func_type(id, FuncKind::Free)?,
            ))))
        }
    }

    fn component_type(&mut self, id: wasm::ComponentTypeId) -> Result<WorldId> {
        let key = self.cache.key(
            None,
            wasm::AnyTypeId::Component(wasm::ComponentAnyTypeId::Component(id)),
        );
        if let Some(ty) = self.cache.get(&key) {
            match ty {
                Type::World(id) => return Ok(id),
                _ => unreachable!("invalid cached type"),
            }
        }

        let types = self.types.clone();
        let component_ty = &types[id];
        let mut imports = IndexMap::with_capacity(component_ty.imports.len());
        for (name, ty) in &component_ty.imports {
            let export = match ty {
                wasm::ComponentEntityType::Type { referenced, .. } => {
                    let ty = self.resolve_alias(*referenced);
                    let converted_ty = self.ty(ty)?;
                    let interface = self.owners.get(&ty).copied();
                    match (interface, converted_ty) {
                        (Some((interface, index)), Type::Value(ty)) => Extern::Use {
                            interface,
                            export_index: index,
                            ty,
                        },
                        _ => Extern::Kind(ItemKind::Type(converted_ty)),
                    }
                }
                wasm::ComponentEntityType::Func(ty) => {
                    match self.resource_method_or_func(&component_ty.imports, name, *ty)? {
                        Some(export) => export,
                        None => continue,
                    }
                }
                _ => Extern::Kind(self.component_entity_type(name, *ty)?),
            };

            let prev = imports.insert(name.clone(), export);
            assert!(prev.is_none());
        }

        let exports = component_ty
            .exports
            .iter()
            .map(|(name, ty)| {
                Ok((
                    name.clone(),
                    Extern::Kind(self.component_entity_type(name, *ty)?),
                ))
            })
            .collect::<Result<_>>()?;

        let id = self.definitions.worlds.alloc(World {
            imports,
            exports,
            scope: None,
        });

        self.cache.insert(key, Type::World(id));
        Ok(id)
    }

    fn component_defined_type(
        &mut self,
        id: wasm::ComponentDefinedTypeId,
    ) -> Result<DefinedTypeId> {
        let key = self.cache.key(
            None,
            wasm::AnyTypeId::Component(wasm::ComponentAnyTypeId::Defined(id)),
        );
        if let Some(ty) = self.cache.get(&key) {
            match ty {
                Type::Value(id) => return Ok(id),
                _ => unreachable!("invalid cached type"),
            }
        }

        let types = self.types.clone();
        let id = match &types[id] {
            wasm::ComponentDefinedType::Primitive(ty) => self
                .definitions
                .types
                .alloc(DefinedType::Primitive((*ty).into())),
            wasm::ComponentDefinedType::Record(ty) => {
                let fields = ty
                    .fields
                    .iter()
                    .map(|(name, ty)| Ok((name.as_str().to_owned(), self.component_val_type(*ty)?)))
                    .collect::<Result<_>>()?;

                self.definitions
                    .types
                    .alloc(DefinedType::Record(Record { fields }))
            }
            wasm::ComponentDefinedType::Variant(ty) => {
                let cases = ty
                    .cases
                    .iter()
                    .map(|(name, case)| {
                        Ok((
                            name.as_str().to_owned(),
                            case.ty.map(|ty| self.component_val_type(ty)).transpose()?,
                        ))
                    })
                    .collect::<Result<_>>()?;

                self.definitions
                    .types
                    .alloc(DefinedType::Variant(Variant { cases }))
            }
            wasm::ComponentDefinedType::List(ty) => {
                let ty = self.component_val_type(*ty)?;
                self.definitions.types.alloc(DefinedType::List(ty))
            }
            wasm::ComponentDefinedType::Tuple(ty) => {
                let types = ty
                    .types
                    .iter()
                    .map(|ty| self.component_val_type(*ty))
                    .collect::<Result<_>>()?;
                self.definitions.types.alloc(DefinedType::Tuple(types))
            }
            wasm::ComponentDefinedType::Flags(flags) => {
                let flags = flags.iter().map(|flag| flag.as_str().to_owned()).collect();
                self.definitions
                    .types
                    .alloc(DefinedType::Flags(Flags(flags)))
            }
            wasm::ComponentDefinedType::Enum(cases) => {
                let cases = cases.iter().map(|case| case.as_str().to_owned()).collect();
                self.definitions.types.alloc(DefinedType::Enum(Enum(cases)))
            }
            wasm::ComponentDefinedType::Option(ty) => {
                let ty = self.component_val_type(*ty)?;
                self.definitions.types.alloc(DefinedType::Option(ty))
            }
            wasm::ComponentDefinedType::Result { ok, err } => {
                let ok = ok.map(|ty| self.component_val_type(ty)).transpose()?;
                let err = err.map(|ty| self.component_val_type(ty)).transpose()?;
                self.definitions
                    .types
                    .alloc(DefinedType::Result { ok, err })
            }
            wasm::ComponentDefinedType::Borrow(id) => {
                let id = self.resources[&self
                    .mapper
                    .get(id.resource())
                    .expect("resource should be mapped")];
                match self.definitions.types[id] {
                    DefinedType::Resource(id) => {
                        self.definitions.types.alloc(DefinedType::Borrow(id))
                    }
                    _ => unreachable!("expected type to be a resource type"),
                }
            }
            wasm::ComponentDefinedType::Own(id) => {
                self.resources[&self
                    .mapper
                    .get(id.resource())
                    .expect("resource should be mapped")]
            }
        };

        self.cache.insert(key, Type::Value(id));
        Ok(id)
    }

    fn resource(&mut self, id: wasm::AliasableResourceId) -> DefinedTypeId {
        let key = self.cache.key(
            None,
            wasm::AnyTypeId::Component(wasm::ComponentAnyTypeId::Resource(id)),
        );
        if let Some(ty) = self.cache.get(&key) {
            match ty {
                Type::Value(id) => return id,
                _ => unreachable!("invalid cached type"),
            }
        }

        let res = id.resource();
        let id =
            self.definitions
                .types
                .alloc(DefinedType::Resource(self.definitions.resources.alloc(
                    Resource {
                        methods: Default::default(),
                    },
                )));
        let internal_id = self.mapper.get(res).expect("resource should be mapped");
        let prev = self.resources.insert(internal_id, id);
        assert!(prev.is_none(), "duplicate resource");

        self.cache.insert(key, Type::Value(id));
        id
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

    fn resolve_alias(&self, id: wasm::ComponentAnyTypeId) -> wasm::AnyTypeId {
        let mut cur = id;
        loop {
            cur = match self.types.peel_alias(cur) {
                Some(next) => next,
                None => break,
            };
        }

        wasm::AnyTypeId::Component(cur)
    }
}
