use super::{
    package::{Package, PackageKey},
    Composition, DefinedType, Definitions, Enum, Error, ExternKind, Flags, Func, FuncId, FuncKind,
    FuncResult, Interface, InterfaceId, ItemKind, PrimitiveType, Record, ResolutionResult,
    Resource, ResourceId, SubtypeChecker, Type, ValueType, Variant, World, WorldId,
};
use crate::{ast, method_extern_name, InstanceOperation, Item, ItemId, PackageId, UsedType};
use anyhow::Context;
use id_arena::Arena;
use indexmap::{IndexMap, IndexSet};
use miette::SourceSpan;
use semver::Version;
use std::{
    collections::{hash_map, HashMap, HashSet},
    sync::Arc,
};
use wasmparser::{
    names::{ComponentName, ComponentNameKind},
    BinaryReaderError,
};

#[derive(Default)]
struct Scope {
    names: IndexMap<String, (ItemId, SourceSpan)>,
    items: Arena<Item>,
}

impl Scope {
    fn get(&self, name: &str) -> Option<(ItemId, SourceSpan)> {
        self.names.get(name).copied()
    }
}

struct Import<'a> {
    /// The package that caused the import.
    /// This is `None` for explicit imports.
    package: Option<&'a str>,
    /// The span where the import was first introduced.
    span: SourceSpan,
    /// The imported item.
    item: ItemId,
}

struct Export {
    /// The span where the export was first introduced.
    span: SourceSpan,
    /// The exported item.
    item: ItemId,
}

struct State<'a> {
    scopes: Vec<Scope>,
    current: Scope,
    packages: Arena<Package>,
    /// The map of package name to id.
    package_map: HashMap<PackageKey<'a>, PackageId>,
    /// The map of instance items and their aliased items.
    aliases: HashMap<ItemId, HashMap<String, ItemId>>,
    /// The map of imported items.
    /// This is used to keep track of implicit imports and merge them together.
    imports: IndexMap<String, Import<'a>>,
    /// The map of exported items.
    exports: IndexMap<String, Export>,
}

impl<'a> State<'a> {
    fn new() -> Self {
        Self {
            scopes: Default::default(),
            current: Default::default(),
            packages: Default::default(),
            package_map: Default::default(),
            aliases: Default::default(),
            imports: Default::default(),
            exports: Default::default(),
        }
    }

    // Gets an item by identifier from the root scope.
    fn root_item(&self, id: &ast::Ident<'a>) -> ResolutionResult<(ItemId, &Item)> {
        let scope = self.root_scope();

        let id = scope
            .get(id.string)
            .ok_or(Error::UndefinedName {
                name: id.string.to_owned(),
                span: id.span,
            })?
            .0;

        Ok((id, &scope.items[id]))
    }

    /// Gets an item by identifier from the local (current) scope.
    fn local_item(&self, id: &ast::Ident<'a>) -> ResolutionResult<(ItemId, &Item)> {
        let id = self
            .current
            .get(id.string)
            .ok_or(Error::UndefinedName {
                name: id.string.to_owned(),
                span: id.span,
            })?
            .0;

        Ok((id, &self.current.items[id]))
    }

    /// Gets an item by identifier from the local (current) scope or the root scope.
    fn local_or_root_item(&self, id: &ast::Ident<'a>) -> ResolutionResult<(ItemId, &Item)> {
        if self.scopes.is_empty() {
            return self.local_item(id);
        }

        if let Some((id, _)) = self.current.get(id.string) {
            return Ok((id, &self.current.items[id]));
        }

        self.root_item(id)
    }

    fn push_scope(&mut self) {
        log::debug!("pushing new name scope");
        self.scopes.push(std::mem::take(&mut self.current));
    }

    fn pop_scope(&mut self) -> Scope {
        log::debug!("popping name scope");
        std::mem::replace(&mut self.current, self.scopes.pop().unwrap())
    }

    fn root_scope(&self) -> &Scope {
        self.scopes.first().unwrap_or(&self.current)
    }

    fn register_name(&mut self, id: ast::Ident<'a>, item: ItemId) -> ResolutionResult<()> {
        log::debug!(
            "registering name `{id}` for item {item} in the current scope",
            id = id.string,
            item = item.index()
        );
        if let Some((_, span)) = self
            .current
            .names
            .insert(id.string.to_owned(), (item, id.span))
        {
            return Err(Error::DuplicateName {
                name: id.string.to_owned(),
                span: id.span,
                previous: span,
            });
        }

        Ok(())
    }
}

pub struct AstResolver<'a> {
    document: &'a ast::Document<'a>,
    definitions: Definitions,
    packages: IndexMap<PackageKey<'a>, Arc<Vec<u8>>>,
}

impl<'a> AstResolver<'a> {
    pub fn new(
        document: &'a ast::Document<'a>,
        packages: IndexMap<PackageKey<'a>, Arc<Vec<u8>>>,
    ) -> Self {
        Self {
            document,
            definitions: Default::default(),
            packages,
        }
    }

    pub fn resolve(mut self) -> ResolutionResult<Composition> {
        let mut state = State::new();

        for stmt in &self.document.statements {
            match stmt {
                ast::Statement::Import(i) => self.import_statement(&mut state, i)?,
                ast::Statement::Type(t) => self.type_statement(&mut state, t)?,
                ast::Statement::Let(l) => self.let_statement(&mut state, l)?,
                ast::Statement::Export(e) => self.export_statement(&mut state, e)?,
            }
        }

        // If there's a target world in the directive, validate the composition
        // conforms to the target
        if let Some(path) = &self.document.directive.targets {
            log::debug!("validating composition targets world `{}`", path.string);
            let item = self.resolve_package_export(&mut state, path)?;
            match item {
                ItemKind::Type(Type::World(world)) => {
                    self.validate_target(&state, path, world)?;
                }
                _ => {
                    return Err(Error::NotWorld {
                        name: path.string.to_owned(),
                        kind: item.as_str(&self.definitions).to_owned(),
                        span: path.span,
                    });
                }
            }
        }

        assert!(state.scopes.is_empty());

        Ok(Composition {
            package: self.document.directive.package.name.to_owned(),
            version: self.document.directive.package.version.clone(),
            definitions: self.definitions,
            packages: state.packages,
            items: state.current.items,
            imports: state
                .imports
                .into_iter()
                .map(|(k, v)| (k, v.item))
                .collect(),
            exports: state
                .exports
                .into_iter()
                .map(|(k, v)| (k, v.item))
                .collect(),
        })
    }

    fn import_statement(
        &mut self,
        state: &mut State<'a>,
        stmt: &'a ast::ImportStatement<'a>,
    ) -> ResolutionResult<()> {
        log::debug!(
            "resolving import statement for id `{id}`",
            id = stmt.id.string
        );
        let (kind, span) = match &stmt.ty {
            ast::ImportType::Package(p) => (self.resolve_package_export(state, p)?, p.span),
            ast::ImportType::Func(ty) => (
                ItemKind::Func(self.func_type(
                    state,
                    &ty.params,
                    &ty.results,
                    FuncKind::Free,
                    None,
                )?),
                stmt.id.span,
            ),
            ast::ImportType::Interface(i) => (self.inline_interface(state, i)?, stmt.id.span),
            ast::ImportType::Ident(id) => (state.local_item(id)?.1.kind(), stmt.id.span),
        };

        // Promote any types to their corresponding item kind
        let kind = kind.promote();

        let (name, span) = if let Some(name) = &stmt.name {
            // Override the span to the `as` clause string
            (name.as_str(), name.span())
        } else {
            // If the item is an instance with an id, use the id
            if let ItemKind::Instance(id) = kind {
                if let Some(id) = &self.definitions.interfaces[id].id {
                    (id.as_str(), span)
                } else {
                    (stmt.id.string, span)
                }
            } else {
                (stmt.id.string, span)
            }
        };

        // Validate the import name
        ComponentName::new(name, 0).map_err(|e| {
            let msg = e.to_string();
            Error::InvalidExternName {
                name: name.to_string(),
                kind: ExternKind::Import,
                span,
                source: anyhow::anyhow!(
                    "{msg}",
                    msg = msg.strip_suffix(" (at offset 0x0)").unwrap_or(&msg)
                ),
            }
        })?;

        if let Some(existing) = state.imports.get(name) {
            match &state.current.items[existing.item] {
                Item::Import { .. } => {
                    if let Some(Import {
                        package: Some(package),
                        span: prev_span,
                        ..
                    }) = state.imports.get(name)
                    {
                        return Err(Error::ImportConflict {
                            name: name.to_string(),
                            package: package.to_string(),
                            span,
                            instantiation: *prev_span,
                        });
                    }

                    return Err(Error::DuplicateExternName {
                        name: name.to_owned(),
                        kind: ExternKind::Import,
                        span,
                        previous: existing.span,
                        help: if stmt.name.is_some() {
                            None
                        } else {
                            Some("consider using an `as` clause to use a different name".into())
                        },
                    });
                }
                _ => unreachable!(),
            }
        }

        let id = state.current.items.alloc(Item::Import(super::Import {
            name: name.to_owned(),
            kind,
        }));

        state.imports.insert(
            name.to_owned(),
            Import {
                package: None,
                span,
                item: id,
            },
        );

        state.register_name(stmt.id, id)
    }

    fn type_statement(
        &mut self,
        state: &mut State<'a>,
        stmt: &'a ast::TypeStatement<'a>,
    ) -> ResolutionResult<()> {
        log::debug!("resolving type statement");

        let (id, item) = match stmt {
            ast::TypeStatement::Interface(i) => (i.id, self.interface_decl(state, i)?),
            ast::TypeStatement::World(w) => (w.id, self.world_decl(state, w)?),
            ast::TypeStatement::Type(t) => (*t.id(), self.type_decl(state, t)?),
        };

        let prev = state.exports.insert(
            id.string.to_owned(),
            Export {
                span: id.span,
                item,
            },
        );
        assert!(prev.is_none());
        Ok(())
    }

    fn let_statement(
        &mut self,
        state: &mut State<'a>,
        stmt: &'a ast::LetStatement<'a>,
    ) -> ResolutionResult<()> {
        log::debug!(
            "resolving type statement for id `{id}`",
            id = stmt.id.string
        );
        let item = self.expr(state, &stmt.expr)?;
        state.register_name(stmt.id, item)
    }

    fn export_statement(
        &mut self,
        state: &mut State<'a>,
        stmt: &'a ast::ExportStatement<'a>,
    ) -> ResolutionResult<()> {
        log::debug!("resolving export statement");

        let item = self.expr(state, &stmt.expr)?;

        match &stmt.options {
            ast::ExportOptions::None => {
                let name = self
                    .infer_export_name(state, item)
                    .ok_or(Error::ExportRequiresAs {
                        span: stmt.expr.span,
                    })?;

                self.export_item(state, item, name.to_owned(), stmt.expr.span, true)?;
            }
            ast::ExportOptions::Spread(span) => {
                let exports =
                    self.instance_exports(state, item, stmt.expr.span, InstanceOperation::Spread)?;

                let mut exported = false;
                for name in exports.keys() {
                    // Only export the item if it another item with the same name
                    // has not been already exported
                    if state.exports.contains_key(name) {
                        continue;
                    }

                    let item = self
                        .alias_export(state, item, exports, name)?
                        .expect("expected a matching export name");

                    self.export_item(state, item, name.clone(), *span, false)?;
                    exported = true;
                }

                if !exported {
                    return Err(Error::SpreadExportNoEffect {
                        span: stmt.expr.span,
                    });
                }
            }
            ast::ExportOptions::Rename(name) => {
                self.export_item(state, item, name.as_str().to_owned(), name.span(), false)?;
            }
        }

        Ok(())
    }

    fn export_item(
        &self,
        state: &mut State<'a>,
        item: ItemId,
        name: String,
        span: SourceSpan,
        show_hint: bool,
    ) -> Result<(), Error> {
        let map_err = |e: BinaryReaderError| {
            let msg = e.to_string();
            Error::InvalidExternName {
                name: name.clone(),
                kind: ExternKind::Export,
                span,
                source: anyhow::anyhow!(
                    "{msg}",
                    msg = msg.strip_suffix(" (at offset 0x0)").unwrap_or(&msg)
                ),
            }
        };

        match ComponentName::new(&name, 0).map_err(map_err)?.kind() {
            ComponentNameKind::Hash(_)
            | ComponentNameKind::Url(_)
            | ComponentNameKind::Dependency(_) => {
                return Err(Error::InvalidExternName {
                    name: name.to_string(),
                    kind: ExternKind::Export,
                    span,
                    source: anyhow::anyhow!("export name cannot be a hash, url, or dependency"),
                });
            }
            _ => {}
        }

        if let Some((item_id, prev_span)) = state.root_scope().get(&name) {
            let item = &state.current.items[item_id];
            if let Item::Definition(definition) = item {
                return Err(Error::ExportConflict {
                    name: name.to_owned(),
                    kind: definition.kind.as_str(&self.definitions).to_string(),
                    span,
                    definition: prev_span,
                    help: if !show_hint {
                        None
                    } else {
                        Some("consider using an `as` clause to use a different name".into())
                    },
                });
            }
        }

        if let Some(existing) = state.exports.get(&name) {
            return Err(Error::DuplicateExternName {
                name: name.to_owned(),
                kind: ExternKind::Export,
                span,
                previous: existing.span,
                help: if !show_hint {
                    None
                } else {
                    Some("consider using an `as` clause to use a different name".into())
                },
            });
        }

        let prev = state.exports.insert(name, Export { span, item });
        assert!(prev.is_none());
        Ok(())
    }

    fn inline_interface(
        &mut self,
        state: &mut State<'a>,
        iface: &'a ast::InlineInterface<'a>,
    ) -> ResolutionResult<ItemKind> {
        log::debug!("resolving inline interface");

        state.push_scope();

        let mut ty = Interface {
            id: None,
            remapped_types: Default::default(),
            uses: Default::default(),
            exports: Default::default(),
        };

        self.interface_items(state, None, &iface.items, &mut ty)?;

        state.pop_scope();

        Ok(ItemKind::Type(Type::Interface(
            self.definitions.interfaces.alloc(ty),
        )))
    }

    fn id(&self, name: &str) -> String {
        format!(
            "{pkg}/{name}{version}",
            pkg = self.document.directive.package.name,
            version = if let Some(version) = &self.document.directive.package.version {
                format!("@{version}")
            } else {
                String::new()
            }
        )
    }

    fn interface_decl(
        &mut self,
        state: &mut State<'a>,
        decl: &'a ast::InterfaceDecl<'a>,
    ) -> ResolutionResult<ItemId> {
        log::debug!(
            "resolving interface declaration for id `{id}`",
            id = decl.id.string
        );
        state.push_scope();

        let mut ty = Interface {
            id: Some(self.id(decl.id.string)),
            remapped_types: Default::default(),
            uses: Default::default(),
            exports: Default::default(),
        };

        self.interface_items(state, Some(decl.id.string), &decl.items, &mut ty)?;

        state.pop_scope();

        let ty = self.definitions.interfaces.alloc(ty);

        let id = state
            .current
            .items
            .alloc(Item::Definition(super::Definition {
                name: decl.id.string.to_owned(),
                kind: ItemKind::Type(Type::Interface(ty)),
            }));

        state.register_name(decl.id, id)?;
        Ok(id)
    }

    fn world_decl(
        &mut self,
        state: &mut State<'a>,
        decl: &'a ast::WorldDecl<'a>,
    ) -> ResolutionResult<ItemId> {
        log::debug!(
            "resolving world declaration for id `{id}`",
            id = decl.id.string
        );
        state.push_scope();

        let mut ty = World {
            id: Some(self.id(decl.id.string)),
            uses: Default::default(),
            imports: Default::default(),
            exports: Default::default(),
        };

        self.world_items(state, decl.id.string, &decl.items, &mut ty)?;

        state.pop_scope();

        let ty = self.definitions.worlds.alloc(ty);

        let id = state
            .current
            .items
            .alloc(Item::Definition(super::Definition {
                name: decl.id.string.to_owned(),
                kind: ItemKind::Type(Type::World(ty)),
            }));

        state.register_name(decl.id, id)?;
        Ok(id)
    }

    fn interface_items(
        &mut self,
        state: &mut State<'a>,
        name: Option<&'a str>,
        items: &'a [ast::InterfaceItem<'a>],
        ty: &mut Interface,
    ) -> ResolutionResult<()> {
        for item in items {
            match item {
                ast::InterfaceItem::Use(u) => {
                    self.use_type(state, u, &mut ty.uses, &mut ty.exports, false)?
                }
                ast::InterfaceItem::Type(decl) => {
                    self.item_type_decl(state, decl, &mut ty.exports)?;
                }
                ast::InterfaceItem::Export(e) => {
                    let kind = ItemKind::Func(self.func_type_ref(state, &e.ty, FuncKind::Free)?);
                    if ty.exports.insert(e.id.string.into(), kind).is_some() {
                        return Err(Error::DuplicateInterfaceExport {
                            name: e.id.string.to_owned(),
                            interface_name: name.map(ToOwned::to_owned),
                            span: e.id.span,
                        });
                    }
                }
            }
        }

        Ok(())
    }

    fn world_items(
        &mut self,
        state: &mut State<'a>,
        world: &'a str,
        items: &'a [ast::WorldItem<'a>],
        ty: &mut World,
    ) -> ResolutionResult<()> {
        let mut includes = Vec::new();
        for item in items {
            match item {
                ast::WorldItem::Use(u) => {
                    self.use_type(state, u, &mut ty.uses, &mut ty.imports, true)?
                }
                ast::WorldItem::Type(decl) => {
                    self.item_type_decl(state, decl, &mut ty.imports)?;
                }
                ast::WorldItem::Import(i) => {
                    self.world_item_path(state, &i.path, ExternKind::Import, world, ty)?
                }
                ast::WorldItem::Export(e) => {
                    self.world_item_path(state, &e.path, ExternKind::Export, world, ty)?
                }
                ast::WorldItem::Include(i) => {
                    // We delay processing includes until after all other items have been processed
                    includes.push(i);
                }
            }
        }

        // Process the includes now that all imports and exports have been processed.
        // This allows us to detect conflicts only in explicitly defined items.
        for i in includes {
            self.world_include(state, i, world, ty)?;
        }

        Ok(())
    }

    fn world_item_path(
        &mut self,
        state: &mut State<'a>,
        path: &'a ast::WorldItemPath<'a>,
        kind: ExternKind,
        world: &'a str,
        ty: &mut World,
    ) -> ResolutionResult<()> {
        let (k, v) = match path {
            ast::WorldItemPath::Named(named) => {
                check_name(named.id.string, named.id.span, ty, world, kind)?;

                (
                    named.id.string.into(),
                    match &named.ty {
                        ast::ExternType::Ident(id) => {
                            let item = state.local_or_root_item(id)?.1;
                            match item.kind() {
                                ItemKind::Type(Type::Interface(id)) => ItemKind::Instance(id),
                                ItemKind::Type(Type::Func(id)) => ItemKind::Func(id),
                                kind => {
                                    return Err(Error::NotFuncOrInterface {
                                        name: id.string.to_owned(),
                                        kind: kind.as_str(&self.definitions).to_owned(),
                                        span: id.span,
                                    });
                                }
                            }
                        }
                        ast::ExternType::Func(f) => ItemKind::Func(self.func_type(
                            state,
                            &f.params,
                            &f.results,
                            FuncKind::Free,
                            None,
                        )?),
                        ast::ExternType::Interface(i) => self.inline_interface(state, i)?,
                    },
                )
            }
            ast::WorldItemPath::Ident(id) => {
                let item = state.root_item(id)?.1;
                match item.kind() {
                    ItemKind::Type(Type::Interface(iface_ty_id)) => {
                        let iface_id = self.definitions.interfaces[iface_ty_id]
                            .id
                            .as_ref()
                            .expect("expected an interface id");
                        check_name(iface_id, id.span, ty, world, kind)?;
                        (iface_id.clone(), ItemKind::Instance(iface_ty_id))
                    }
                    kind => {
                        return Err(Error::NotInterface {
                            name: id.string.to_owned(),
                            kind: kind.as_str(&self.definitions).to_owned(),
                            span: id.span,
                        });
                    }
                }
            }

            ast::WorldItemPath::Package(p) => match self.resolve_package_export(state, p)? {
                ItemKind::Type(Type::Interface(id)) => {
                    let name = self.definitions.interfaces[id]
                        .id
                        .as_ref()
                        .expect("expected an interface id");
                    check_name(name, p.span, ty, world, kind)?;
                    (name.clone(), ItemKind::Instance(id))
                }
                kind => {
                    return Err(Error::NotInterface {
                        name: p.string.to_owned(),
                        kind: kind.as_str(&self.definitions).to_owned(),
                        span: p.span,
                    });
                }
            },
        };

        if kind == ExternKind::Import {
            ty.imports.insert(k, v);
        } else {
            ty.exports.insert(k, v);
        }

        return Ok(());

        fn check_name(
            name: &str,
            span: SourceSpan,
            ty: &World,
            world: &str,
            kind: ExternKind,
        ) -> ResolutionResult<()> {
            let exists: bool = if kind == ExternKind::Import {
                ty.imports.contains_key(name)
            } else {
                ty.exports.contains_key(name)
            };

            if exists {
                return Err(Error::DuplicateWorldItem {
                    kind,
                    name: name.to_owned(),
                    world: world.to_owned(),
                    span,
                });
            }

            Ok(())
        }
    }

    fn world_include(
        &mut self,
        state: &mut State<'a>,
        include: &'a ast::WorldInclude<'a>,
        world: &'a str,
        ty: &mut World,
    ) -> ResolutionResult<()> {
        log::debug!("resolving include of world `{world}`");
        let mut replacements = HashMap::new();
        for item in &include.with {
            let prev = replacements.insert(item.from.string, item);
            if prev.is_some() {
                return Err(Error::DuplicateWorldIncludeName {
                    name: item.from.string.to_owned(),
                    span: item.from.span,
                });
            }
        }

        let id = match &include.world {
            ast::WorldRef::Ident(id) => {
                let item = state.root_item(id)?.1;
                match item.kind() {
                    ItemKind::Type(Type::World(id)) | ItemKind::Component(id) => id,
                    kind => {
                        return Err(Error::NotWorld {
                            name: id.string.to_owned(),
                            kind: kind.as_str(&self.definitions).to_owned(),
                            span: id.span,
                        });
                    }
                }
            }
            ast::WorldRef::Package(path) => match self.resolve_package_export(state, path)? {
                ItemKind::Type(Type::World(id)) | ItemKind::Component(id) => id,
                kind => {
                    return Err(Error::NotWorld {
                        name: path.string.to_owned(),
                        kind: kind.as_str(&self.definitions).to_owned(),
                        span: path.span,
                    });
                }
            },
        };

        let other = &self.definitions.worlds[id];
        for (name, item) in &other.imports {
            let name = replace_name(
                include,
                world,
                ty,
                name,
                ExternKind::Import,
                &mut replacements,
            )?;
            ty.imports.entry(name).or_insert(*item);
        }

        for (name, item) in &other.exports {
            let name = replace_name(
                include,
                world,
                ty,
                name,
                ExternKind::Export,
                &mut replacements,
            )?;
            ty.exports.entry(name).or_insert(*item);
        }

        if let Some(missing) = replacements.values().next() {
            return Err(Error::MissingWorldInclude {
                world: include.world.name().to_owned(),
                name: missing.from.string.to_owned(),
                span: missing.from.span,
            });
        }

        return Ok(());

        fn replace_name<'a>(
            include: &ast::WorldInclude<'a>,
            world: &'a str,
            ty: &mut World,
            name: &str,
            kind: ExternKind,
            replacements: &mut HashMap<&str, &ast::WorldIncludeItem<'a>>,
        ) -> ResolutionResult<String> {
            // Check for a id, which doesn't get replaced.
            if name.contains(':') {
                return Ok(name.to_owned());
            }

            let (name, span) = replacements
                .remove(name)
                .map(|i| (i.to.string, i.to.span))
                .unwrap_or_else(|| (name, include.world.span()));

            let exists = if kind == ExternKind::Import {
                ty.imports.contains_key(name)
            } else {
                ty.exports.contains_key(name)
            };

            if exists {
                return Err(Error::WorldIncludeConflict {
                    kind,
                    name: name.to_owned(),
                    from: include.world.name().to_owned(),
                    to: world.to_owned(),
                    span,
                    help: if !include.with.is_empty() {
                        None
                    } else {
                        Some("consider using a `with` clause to use a different name".into())
                    },
                });
            }

            Ok(name.to_owned())
        }
    }

    fn use_type(
        &mut self,
        state: &mut State<'a>,
        use_type: &'a ast::Use<'a>,
        uses: &mut IndexMap<String, UsedType>,
        externs: &mut IndexMap<String, ItemKind>,
        in_world: bool,
    ) -> ResolutionResult<()> {
        let (interface, name) = match &use_type.path {
            ast::UsePath::Package(path) => match self.resolve_package_export(state, path)? {
                ItemKind::Type(Type::Interface(id)) => (id, path.string),
                kind => {
                    return Err(Error::NotInterface {
                        name: path.string.to_owned(),
                        kind: kind.as_str(&self.definitions).to_owned(),
                        span: path.span,
                    });
                }
            },
            ast::UsePath::Ident(id) => {
                let item = state.root_item(id)?.1;
                match item.kind() {
                    ItemKind::Type(Type::Interface(iface_ty_id)) => (iface_ty_id, id.string),
                    kind => {
                        return Err(Error::NotInterface {
                            name: id.string.to_owned(),
                            kind: kind.as_str(&self.definitions).to_owned(),
                            span: id.span,
                        });
                    }
                }
            }
        };

        for item in &use_type.items {
            let ident = item.as_id.unwrap_or(item.id);
            let kind = self.definitions.interfaces[interface]
                .exports
                .get(item.id.string)
                .ok_or(Error::UndefinedInterfaceType {
                    name: item.id.string.to_string(),
                    interface_name: name.to_string(),
                    span: item.id.span,
                })?;

            match kind {
                ItemKind::Resource(_) | ItemKind::Type(Type::Value(_)) => {
                    if externs.contains_key(ident.string) {
                        return Err(Error::UseConflict {
                            name: ident.string.to_string(),
                            kind: if in_world {
                                ExternKind::Import
                            } else {
                                ExternKind::Export
                            },
                            span: ident.span,
                            help: if item.as_id.is_some() {
                                None
                            } else {
                                Some("consider using an `as` clause to use a different name".into())
                            },
                        });
                    }

                    uses.insert(
                        ident.string.into(),
                        UsedType {
                            interface,
                            name: item.as_id.map(|_| item.id.string.to_string()),
                        },
                    );
                    externs.insert(ident.string.into(), *kind);

                    let id = state.current.items.alloc(Item::Use(*kind));
                    state.register_name(ident, id)?;
                }
                _ => {
                    return Err(Error::NotInterfaceValueType {
                        name: item.id.string.to_string(),
                        kind: kind.as_str(&self.definitions).to_string(),
                        interface_name: name.to_string(),
                        span: item.id.span,
                    });
                }
            }
        }

        Ok(())
    }

    fn type_decl(
        &mut self,
        state: &mut State<'a>,
        decl: &'a ast::TypeDecl,
    ) -> ResolutionResult<ItemId> {
        match decl {
            ast::TypeDecl::Variant(v) => self.variant_decl(state, v),
            ast::TypeDecl::Record(r) => self.record_decl(state, r),
            ast::TypeDecl::Flags(f) => self.flags_decl(state, f),
            ast::TypeDecl::Enum(e) => self.enum_decl(state, e),
            ast::TypeDecl::Alias(a) => self.type_alias(state, a),
        }
    }

    fn item_type_decl(
        &mut self,
        state: &mut State<'a>,
        decl: &'a ast::ItemTypeDecl,
        externs: &mut IndexMap<String, ItemKind>,
    ) -> ResolutionResult<ItemId> {
        let (insert, item) = match decl {
            ast::ItemTypeDecl::Resource(r) => (false, self.resource_decl(state, r, externs)?),
            ast::ItemTypeDecl::Variant(v) => (true, self.variant_decl(state, v)?),
            ast::ItemTypeDecl::Record(r) => (true, self.record_decl(state, r)?),
            ast::ItemTypeDecl::Flags(f) => (true, self.flags_decl(state, f)?),
            ast::ItemTypeDecl::Enum(e) => (true, self.enum_decl(state, e)?),
            ast::ItemTypeDecl::Alias(a) => (true, self.type_alias(state, a)?),
        };

        if insert {
            let prev = externs.insert(decl.id().string.into(), state.current.items[item].kind());
            assert!(prev.is_none(), "duplicate type in scope");
        }

        Ok(item)
    }

    fn resource_decl(
        &mut self,
        state: &mut State<'a>,
        decl: &ast::ResourceDecl<'a>,
        externs: &mut IndexMap<String, ItemKind>,
    ) -> ResolutionResult<ItemId> {
        log::debug!(
            "resolving resource declaration for id `{id}`",
            id = decl.id.string
        );

        // Define the resource before resolving the methods
        let id = self.definitions.resources.alloc(Resource {
            name: decl.id.string.to_owned(),
            alias_of: None,
        });

        let kind = ItemKind::Resource(id);
        let item_id = state
            .current
            .items
            .alloc(Item::Definition(super::Definition {
                name: decl.id.string.to_owned(),
                kind,
            }));

        state.register_name(decl.id, item_id)?;

        // We must add the resource to the externs before any methods
        let prev = externs.insert(decl.id.string.into(), kind);
        assert!(prev.is_none());

        let mut names = HashSet::new();
        for method in &decl.methods {
            let (name, ty) = match method {
                ast::ResourceMethod::Constructor(ast::Constructor { span, params, .. }) => {
                    if !names.insert("") {
                        return Err(Error::DuplicateResourceConstructor {
                            resource: decl.id.string.to_string(),
                            span: *span,
                        });
                    }

                    (
                        method_extern_name(decl.id.string, "", FuncKind::Constructor),
                        self.func_type(
                            state,
                            params,
                            &ast::ResultList::Empty,
                            FuncKind::Constructor,
                            Some(id),
                        )?,
                    )
                }
                ast::ResourceMethod::Method(ast::Method {
                    id: method_id,
                    is_static,
                    ty,
                    ..
                }) => {
                    let kind = if *is_static {
                        FuncKind::Static
                    } else {
                        FuncKind::Method
                    };

                    if !names.insert(method_id.string) {
                        return Err(Error::DuplicateResourceMethod {
                            name: method_id.string.to_string(),
                            resource: decl.id.string.to_string(),
                            span: method_id.span,
                        });
                    }

                    (
                        method_extern_name(decl.id.string, method_id.string, kind),
                        self.func_type(state, &ty.params, &ty.results, kind, Some(id))?,
                    )
                }
            };

            let prev = externs.insert(name, ItemKind::Func(ty));
            assert!(prev.is_none());
        }

        Ok(item_id)
    }

    fn variant_decl(
        &mut self,
        state: &mut State<'a>,
        decl: &ast::VariantDecl<'a>,
    ) -> ResolutionResult<ItemId> {
        log::debug!(
            "resolving variant declaration for id `{id}`",
            id = decl.id.string
        );

        let mut cases = IndexMap::new();
        let mut contains_borrow = false;
        for case in &decl.cases {
            let ty = case.ty.as_ref().map(|ty| self.ty(state, ty)).transpose()?;
            contains_borrow |= ty.as_ref().map_or(false, |ty| ty.contains_borrow());
            if cases.insert(case.id.string.into(), ty).is_some() {
                return Err(Error::DuplicateVariantCase {
                    case: case.id.string.to_string(),
                    name: decl.id.string.to_string(),
                    span: case.id.span,
                });
            }
        }

        let kind = ItemKind::Type(Type::Value(ValueType::Defined {
            id: self
                .definitions
                .types
                .alloc(DefinedType::Variant(Variant { cases })),
            contains_borrow,
        }));
        let id = state
            .current
            .items
            .alloc(Item::Definition(super::Definition {
                name: decl.id.string.to_owned(),
                kind,
            }));
        state.register_name(decl.id, id)?;
        Ok(id)
    }

    fn record_decl(
        &mut self,
        state: &mut State<'a>,
        decl: &ast::RecordDecl<'a>,
    ) -> ResolutionResult<ItemId> {
        log::debug!(
            "resolving record declaration for id `{id}`",
            id = decl.id.string
        );

        let mut fields = IndexMap::new();
        let mut contains_borrow = false;
        for field in &decl.fields {
            let ty = self.ty(state, &field.ty)?;
            contains_borrow |= ty.contains_borrow();
            if fields.insert(field.id.string.into(), ty).is_some() {
                return Err(Error::DuplicateRecordField {
                    field: field.id.string.to_string(),
                    name: decl.id.string.to_string(),
                    span: field.id.span,
                });
            }
        }

        let kind = ItemKind::Type(Type::Value(ValueType::Defined {
            id: self
                .definitions
                .types
                .alloc(DefinedType::Record(Record { fields })),
            contains_borrow,
        }));
        let id = state
            .current
            .items
            .alloc(Item::Definition(super::Definition {
                name: decl.id.string.to_owned(),
                kind,
            }));
        state.register_name(decl.id, id)?;
        Ok(id)
    }

    fn flags_decl(
        &mut self,
        state: &mut State<'a>,
        decl: &ast::FlagsDecl<'a>,
    ) -> ResolutionResult<ItemId> {
        log::debug!(
            "resolving flags declaration for id `{id}`",
            id = decl.id.string
        );

        let mut flags = IndexSet::new();
        for flag in &decl.flags {
            if !flags.insert(flag.id.string.into()) {
                return Err(Error::DuplicateFlag {
                    flag: flag.id.string.to_string(),
                    name: decl.id.string.to_string(),
                    span: flag.id.span,
                });
            }
        }

        let kind = ItemKind::Type(Type::Value(ValueType::Defined {
            id: self
                .definitions
                .types
                .alloc(DefinedType::Flags(Flags(flags))),
            contains_borrow: false,
        }));
        let id = state
            .current
            .items
            .alloc(Item::Definition(super::Definition {
                name: decl.id.string.to_owned(),
                kind,
            }));
        state.register_name(decl.id, id)?;
        Ok(id)
    }

    fn enum_decl(
        &mut self,
        state: &mut State<'a>,
        decl: &ast::EnumDecl<'a>,
    ) -> ResolutionResult<ItemId> {
        log::debug!(
            "resolving enum declaration for id `{id}`",
            id = decl.id.string
        );

        let mut cases = IndexSet::new();
        for case in &decl.cases {
            if !cases.insert(case.id.string.to_owned()) {
                return Err(Error::DuplicateEnumCase {
                    case: case.id.string.to_string(),
                    name: decl.id.string.to_string(),
                    span: case.id.span,
                });
            }
        }

        let kind = ItemKind::Type(Type::Value(ValueType::Defined {
            id: self.definitions.types.alloc(DefinedType::Enum(Enum(cases))),
            contains_borrow: false,
        }));
        let id = state
            .current
            .items
            .alloc(Item::Definition(super::Definition {
                name: decl.id.string.to_owned(),
                kind,
            }));

        state.register_name(decl.id, id)?;
        Ok(id)
    }

    fn type_alias(
        &mut self,
        state: &mut State<'a>,
        alias: &ast::TypeAlias<'a>,
    ) -> ResolutionResult<ItemId> {
        log::debug!("resolving type alias for id `{id}`", id = alias.id.string);

        let kind = match &alias.kind {
            ast::TypeAliasKind::Func(f) => ItemKind::Type(Type::Func(self.func_type(
                state,
                &f.params,
                &f.results,
                FuncKind::Free,
                None,
            )?)),
            ast::TypeAliasKind::Type(ty) => match ty {
                ast::Type::Ident(id) => {
                    let item = state.local_item(id)?.1;
                    match item.kind() {
                        ItemKind::Resource(id) => {
                            ItemKind::Resource(self.definitions.resources.alloc(Resource {
                                name: alias.id.string.to_owned(),
                                alias_of: Some(id),
                            }))
                        }
                        ItemKind::Type(Type::Value(ty)) => {
                            ItemKind::Type(Type::Value(ValueType::Defined {
                                id: self.definitions.types.alloc(DefinedType::Alias(ty)),
                                contains_borrow: ty.contains_borrow(),
                            }))
                        }
                        ItemKind::Type(Type::Func(id)) | ItemKind::Func(id) => {
                            ItemKind::Type(Type::Func(id))
                        }
                        kind => {
                            return Err(Error::InvalidAliasType {
                                name: id.string.to_string(),
                                kind: kind.as_str(&self.definitions).to_string(),
                                span: id.span,
                            });
                        }
                    }
                }
                _ => {
                    let ty = self.ty(state, ty)?;
                    ItemKind::Type(Type::Value(ValueType::Defined {
                        id: self.definitions.types.alloc(DefinedType::Alias(ty)),
                        contains_borrow: ty.contains_borrow(),
                    }))
                }
            },
        };

        let id = state
            .current
            .items
            .alloc(Item::Definition(super::Definition {
                name: alias.id.string.to_owned(),
                kind,
            }));
        state.register_name(alias.id, id)?;
        Ok(id)
    }

    fn func_type_ref(
        &mut self,
        state: &State<'a>,
        r: &ast::FuncTypeRef<'a>,
        kind: FuncKind,
    ) -> ResolutionResult<FuncId> {
        match r {
            ast::FuncTypeRef::Func(ty) => {
                self.func_type(state, &ty.params, &ty.results, kind, None)
            }
            ast::FuncTypeRef::Ident(id) => {
                let item = state.local_item(id)?.1;
                match item.kind() {
                    ItemKind::Type(Type::Func(id)) | ItemKind::Func(id) => Ok(id),
                    kind => Err(Error::NotFuncType {
                        name: id.string.to_string(),
                        kind: kind.as_str(&self.definitions).to_string(),
                        span: id.span,
                    }),
                }
            }
        }
    }

    fn ty(&mut self, state: &State<'a>, ty: &ast::Type<'a>) -> ResolutionResult<ValueType> {
        match ty {
            ast::Type::U8(_) => Ok(ValueType::Primitive(PrimitiveType::U8)),
            ast::Type::S8(_) => Ok(ValueType::Primitive(PrimitiveType::S8)),
            ast::Type::U16(_) => Ok(ValueType::Primitive(PrimitiveType::U16)),
            ast::Type::S16(_) => Ok(ValueType::Primitive(PrimitiveType::S16)),
            ast::Type::U32(_) => Ok(ValueType::Primitive(PrimitiveType::U32)),
            ast::Type::S32(_) => Ok(ValueType::Primitive(PrimitiveType::S32)),
            ast::Type::U64(_) => Ok(ValueType::Primitive(PrimitiveType::U64)),
            ast::Type::S64(_) => Ok(ValueType::Primitive(PrimitiveType::S64)),
            ast::Type::F32(_) => Ok(ValueType::Primitive(PrimitiveType::F32)),
            ast::Type::F64(_) => Ok(ValueType::Primitive(PrimitiveType::F64)),
            ast::Type::Char(_) => Ok(ValueType::Primitive(PrimitiveType::Char)),
            ast::Type::Bool(_) => Ok(ValueType::Primitive(PrimitiveType::Bool)),
            ast::Type::String(_) => Ok(ValueType::Primitive(PrimitiveType::String)),
            ast::Type::Tuple(v, _) => {
                let mut contains_borrow = false;
                let types = v
                    .iter()
                    .map(|ty| {
                        let ty = self.ty(state, ty)?;
                        contains_borrow |= ty.contains_borrow();
                        Ok(ty)
                    })
                    .collect::<ResolutionResult<_>>()?;

                Ok(ValueType::Defined {
                    id: self.definitions.types.alloc(DefinedType::Tuple(types)),
                    contains_borrow,
                })
            }
            ast::Type::List(ty, _) => {
                let ty = self.ty(state, ty)?;
                Ok(ValueType::Defined {
                    id: self.definitions.types.alloc(DefinedType::List(ty)),
                    contains_borrow: ty.contains_borrow(),
                })
            }
            ast::Type::Option(ty, _) => {
                let ty = self.ty(state, ty)?;
                Ok(ValueType::Defined {
                    id: self.definitions.types.alloc(DefinedType::Option(ty)),
                    contains_borrow: ty.contains_borrow(),
                })
            }
            ast::Type::Result { ok, err, .. } => {
                let ok = ok.as_ref().map(|t| self.ty(state, t)).transpose()?;
                let err = err.as_ref().map(|t| self.ty(state, t)).transpose()?;
                Ok(ValueType::Defined {
                    id: self
                        .definitions
                        .types
                        .alloc(DefinedType::Result { ok, err }),
                    contains_borrow: ok.as_ref().map_or(false, |t| t.contains_borrow())
                        || err.as_ref().map_or(false, |t| t.contains_borrow()),
                })
            }
            ast::Type::Borrow(id, _) => {
                let item = state.local_item(id)?.1;
                let kind = item.kind();
                if let ItemKind::Resource(id) = kind {
                    return Ok(ValueType::Borrow(id));
                }

                Err(Error::NotResourceType {
                    name: id.string.to_string(),
                    kind: kind.as_str(&self.definitions).to_string(),
                    span: id.span,
                })
            }
            ast::Type::Ident(id) => {
                let item = state.local_item(id)?.1;
                match item.kind() {
                    ItemKind::Resource(id) => Ok(ValueType::Own(id)),
                    ItemKind::Type(Type::Value(ty)) => Ok(ty),
                    kind => Err(Error::NotValueType {
                        name: id.string.to_string(),
                        kind: kind.as_str(&self.definitions).to_string(),
                        span: id.span,
                    }),
                }
            }
        }
    }

    fn func_type(
        &mut self,
        state: &State<'a>,
        func_params: &[ast::NamedType<'a>],
        func_results: &ast::ResultList<'a>,
        kind: FuncKind,
        resource: Option<ResourceId>,
    ) -> ResolutionResult<FuncId> {
        let mut params = IndexMap::new();

        if kind == FuncKind::Method {
            params.insert("self".into(), ValueType::Borrow(resource.unwrap()));
        }

        for param in func_params {
            if params
                .insert(param.id.string.into(), self.ty(state, &param.ty)?)
                .is_some()
            {
                return Err(Error::DuplicateParameter {
                    name: param.id.string.to_string(),
                    kind,
                    span: param.id.span,
                });
            }
        }

        let results = match func_results {
            ast::ResultList::Empty => {
                if kind == FuncKind::Constructor {
                    Some(FuncResult::Scalar(ValueType::Own(resource.unwrap())))
                } else {
                    None
                }
            }
            ast::ResultList::Named(results) => {
                let mut list = IndexMap::new();
                for result in results {
                    let value_type = self.ty(state, &result.ty)?;
                    if value_type.contains_borrow() {
                        return Err(Error::BorrowInResult {
                            span: result.ty.span(),
                        });
                    }

                    if list
                        .insert(result.id.string.to_owned(), value_type)
                        .is_some()
                    {
                        return Err(Error::DuplicateResult {
                            name: result.id.string.to_string(),
                            kind,
                            span: result.id.span,
                        });
                    }
                }
                Some(FuncResult::List(list))
            }
            ast::ResultList::Scalar(ty) => {
                let value_type = self.ty(state, ty)?;
                if value_type.contains_borrow() {
                    return Err(Error::BorrowInResult { span: ty.span() });
                }
                Some(FuncResult::Scalar(value_type))
            }
        };

        Ok(self.definitions.funcs.alloc(Func { params, results }))
    }

    fn resolve_package(
        &mut self,
        state: &mut State<'a>,
        name: &'a str,
        version: Option<&'a Version>,
        span: SourceSpan,
    ) -> ResolutionResult<PackageId> {
        match state.package_map.entry(PackageKey { name, version }) {
            hash_map::Entry::Occupied(e) => Ok(*e.get()),
            hash_map::Entry::Vacant(e) => {
                log::debug!("resolving package `{name}`");
                let bytes = match self.packages.get(&PackageKey { name, version }) {
                    Some(bytes) => bytes.clone(),
                    None => {
                        return Err(Error::UnknownPackage {
                            name: name.to_string(),
                            span,
                        })
                    }
                };

                let id = state.packages.alloc(
                    Package::parse(&mut self.definitions, name, version, bytes).map_err(|e| {
                        Error::PackageParseFailure {
                            name: name.to_string(),
                            span,
                            source: e,
                        }
                    })?,
                );
                Ok(*e.insert(id))
            }
        }
    }

    fn resolve_package_export(
        &mut self,
        state: &mut State<'a>,
        path: &'a ast::PackagePath<'a>,
    ) -> ResolutionResult<ItemKind> {
        log::debug!("resolving package export `{}`", path.string);
        // Check for reference to local item
        if path.name == self.document.directive.package.name {
            return self.resolve_local_export(state, path);
        }

        let pkg = self.resolve_package(
            state,
            path.name,
            path.version.as_ref(),
            path.package_name_span(),
        )?;

        let mut current = 0;
        let mut parent_ty = None;
        let mut found = None;
        for (i, (segment, _)) in path.segment_spans().enumerate() {
            current = i;

            // Look up the first segment in the package definitions
            if i == 0 {
                found = state.packages[pkg].definitions.get(segment).copied();
                continue;
            }

            // Otherwise, project into the parent based on the current segment
            let export = match found.unwrap() {
                // The parent is an interface or instance
                ItemKind::Type(Type::Interface(id)) | ItemKind::Instance(id) => {
                    self.definitions.interfaces[id]
                        .exports
                        .get(segment)
                        .copied()
                }
                // The parent is a world or component or component instantiation
                ItemKind::Type(Type::World(id)) | ItemKind::Component(id) => {
                    self.definitions.worlds[id].exports.get(segment).copied()
                }
                _ => None,
            };

            parent_ty = found.map(|kind| kind.as_str(&self.definitions));
            found = export;
            if found.is_none() {
                break;
            }
        }

        found.ok_or_else(|| {
            let segments = path.segment_spans().enumerate();
            let mut prev_path = String::new();
            for (i, (segment, span)) in segments {
                if i == current {
                    return Error::PackageMissingExport {
                        name: path.string.to_string(),
                        export: segment.to_string(),
                        kind: parent_ty.map(ToOwned::to_owned),
                        path: prev_path,
                        span,
                    };
                }

                if !prev_path.is_empty() {
                    prev_path.push('/');
                }

                prev_path.push_str(segment);
            }

            unreachable!("path segments should never be empty")
        })
    }

    fn resolve_local_export(
        &self,
        state: &State<'a>,
        path: &ast::PackagePath<'a>,
    ) -> ResolutionResult<ItemKind> {
        log::debug!("resolving local path `{path}`", path = path.string);

        let mut segments = path.segment_spans();
        let (segment, span) = segments.next().unwrap();
        let item = state
            .root_item(&ast::Ident {
                string: segment,
                span,
            })?
            .1;

        let mut current = segment;
        let mut kind = item.kind();
        for (segment, span) in segments {
            let exports = match kind {
                ItemKind::Type(Type::Interface(id)) | ItemKind::Instance(id) => {
                    &self.definitions.interfaces[id].exports
                }
                ItemKind::Type(Type::World(id)) | ItemKind::Component(id) => {
                    &self.definitions.worlds[id].exports
                }
                _ => {
                    return Err(Error::PackagePathMissingExport {
                        name: current.to_string(),
                        kind: kind.as_str(&self.definitions).to_string(),
                        export: segment.to_string(),
                        span,
                    });
                }
            };

            kind =
                exports
                    .get(segment)
                    .copied()
                    .ok_or_else(|| Error::PackagePathMissingExport {
                        name: current.to_string(),
                        kind: kind.as_str(&self.definitions).to_string(),
                        export: segment.to_string(),
                        span,
                    })?;

            current = segment;
        }

        Ok(kind)
    }

    fn expr(&mut self, state: &mut State<'a>, expr: &'a ast::Expr<'a>) -> ResolutionResult<ItemId> {
        let mut item = self.primary_expr(state, &expr.primary)?;

        let mut parent_span = expr.primary.span();
        for expr in &expr.postfix {
            item = self.postfix_expr(state, item, expr, parent_span)?;
            parent_span = expr.span();
        }

        Ok(item)
    }

    fn primary_expr(
        &mut self,
        state: &mut State<'a>,
        expr: &'a ast::PrimaryExpr<'a>,
    ) -> ResolutionResult<ItemId> {
        match expr {
            ast::PrimaryExpr::New(e) => self.new_expr(state, e),
            ast::PrimaryExpr::Nested(e) => self.expr(state, &e.inner),
            ast::PrimaryExpr::Ident(i) => Ok(state.local_item(i)?.0),
        }
    }

    fn new_expr(
        &mut self,
        state: &mut State<'a>,
        expr: &'a ast::NewExpr<'a>,
    ) -> ResolutionResult<ItemId> {
        if expr.package.name == self.document.directive.package.name {
            return Err(Error::UnknownPackage {
                name: expr.package.name.to_string(),
                span: expr.package.span,
            });
        }

        let pkg = self.resolve_package(
            state,
            expr.package.name,
            expr.package.version.as_ref(),
            expr.package.span,
        )?;
        let ty = state.packages[pkg].world;
        let mut require_all = true;

        let mut arguments: IndexMap<String, (ItemId, SourceSpan)> = Default::default();
        for (i, arg) in expr.arguments.iter().enumerate() {
            let (name, item, span) = match arg {
                ast::InstantiationArgument::Inferred(id) => {
                    self.inferred_instantiation_arg(state, id, ty)?
                }
                ast::InstantiationArgument::Spread(_) => {
                    // Spread arguments will be processed after all other arguments
                    continue;
                }
                ast::InstantiationArgument::Named(arg) => {
                    self.named_instantiation_arg(state, arg, ty)?
                }
                ast::InstantiationArgument::Fill(span) => {
                    if i != (expr.arguments.len() - 1) {
                        return Err(Error::FillArgumentNotLast { span: *span });
                    }

                    require_all = false;
                    continue;
                }
            };

            let prev = arguments.insert(name.clone(), (item, span));
            if prev.is_some() {
                return Err(Error::DuplicateInstantiationArg { name, span });
            }
        }

        // Process the spread arguments
        for arg in &expr.arguments {
            if let ast::InstantiationArgument::Spread(id) = arg {
                self.spread_instantiation_arg(state, id, ty, &mut arguments)?;
            }
        }

        // Type check the arguments
        for (name, (item, span)) in &arguments {
            let world = &self.definitions.worlds[ty];
            let expected =
                world
                    .imports
                    .get(name)
                    .ok_or_else(|| Error::MissingComponentImport {
                        package: expr.package.string.to_string(),
                        import: name.clone(),
                        span: *span,
                    })?;

            log::debug!(
                "performing subtype check for argument `{name}` (item {item})",
                item = item.index()
            );

            SubtypeChecker::new(&self.definitions, &state.packages)
                .is_subtype(state.current.items[*item].kind(), *expected)
                .map_err(|e| Error::MismatchedInstantiationArg {
                    name: name.clone(),
                    span: *span,
                    source: e,
                })?;
        }

        // Add implicit imports (i.e. `...` was present) or error in
        // case of missing imports
        let world = &self.definitions.worlds[ty];
        let missing = world
            .imports
            .iter()
            .filter(|(n, _)| !arguments.contains_key(n.as_str()))
            .map(|(n, k)| (n.clone(), *k))
            .collect::<Vec<_>>();
        for (name, argument) in missing {
            if require_all {
                return Err(Error::MissingInstantiationArg {
                    name,
                    package: expr.package.string.to_string(),
                    span: expr.package.span,
                });
            }

            // Implicitly import the argument
            let item = self.implicit_import(
                state,
                name.clone(),
                argument,
                expr.package.name,
                expr.package.span,
            )?;

            arguments.insert(name, (item, expr.package.span));
        }

        Ok(state
            .current
            .items
            .alloc(Item::Instantiation(super::Instantiation {
                package: pkg,
                arguments: arguments.into_iter().map(|(n, (i, _))| (n, i)).collect(),
            })))
    }

    fn implicit_import(
        &mut self,
        state: &mut State<'a>,
        name: String,
        mut kind: ItemKind,
        package: &'a str,
        span: SourceSpan,
    ) -> ResolutionResult<ItemId> {
        assert!(state.scopes.is_empty());

        if let Some(import) = state.imports.get(&name) {
            // Check if the implicit import would conflict with an explicit import
            if import.package.is_none() {
                return Err(Error::InstantiationArgConflict {
                    name,
                    kind: kind.as_str(&self.definitions).to_string(),
                    span,
                    import: import.span,
                });
            };

            // Merge the existing import item with the given one
            return match (kind, state.current.items[import.item].kind()) {
                (ItemKind::Instance(id), ItemKind::Instance(_)) => {
                    log::debug!(
                        "merging implicit interface import `{name}` ({id})",
                        id = id.index(),
                    );

                    let item = import.item;
                    self.merge_instance_import(state, &name, id, span)?;
                    Ok(item)
                }
                (ItemKind::Component(_), ItemKind::Component(_)) => {
                    todo!("merge component imports")
                }
                (ItemKind::Func(_), ItemKind::Func(_)) => {
                    todo!("merge func imports")
                }
                (ItemKind::Module(_), ItemKind::Module(_)) => {
                    todo!("merge module imports")
                }
                (ItemKind::Resource(_), ItemKind::Resource(_)) => {
                    todo!("merge resource imports")
                }
                (ItemKind::Type(_), ItemKind::Type(_)) => {
                    todo!("merge type imports")
                }
                (ItemKind::Value(_), ItemKind::Value(_)) => {
                    todo!("merge value imports")
                }
                (_, kind) => {
                    return Err(Error::UnmergeableInstantiationArg {
                        name,
                        package: import.package.unwrap().to_string(),
                        kind: kind.as_str(&self.definitions).to_string(),
                        span,
                        instantiation: import.span,
                    });
                }
            };
        }

        log::debug!(
            "adding implicit import `{name}` ({kind})",
            kind = kind.as_str(&self.definitions)
        );

        // If the item is an instance, we need to clone the interface as it
        // might be merged in the future with other interface definitions.
        if let ItemKind::Instance(id) = kind {
            let mut target = self.definitions.interfaces[id].clone();
            self.remap_uses(state, &mut target.uses);
            let id = self.definitions.interfaces.alloc(target);
            log::debug!(
                "creating new interface definition ({id}) for implicit import `{name}`",
                id = id.index()
            );
            kind = ItemKind::Instance(id);
        }

        let id = state.current.items.alloc(Item::Import(super::Import {
            name: name.clone(),
            kind,
        }));

        state.imports.insert(
            name,
            Import {
                package: Some(package),
                span,
                item: id,
            },
        );

        Ok(id)
    }

    fn merge_instance_import(
        &mut self,
        state: &mut State<'a>,
        name: &str,
        source_id: InterfaceId,
        span: SourceSpan,
    ) -> ResolutionResult<()> {
        let import = state.imports.get(name).unwrap();
        let import_span = import.span;
        let target_id = match state.current.items[import.item].kind() {
            ItemKind::Instance(id) => id,
            _ => unreachable!(),
        };

        // Merge the used types of the two interfaces
        self.merge_used_types(state, target_id, source_id);

        // Perform the merge of the interfaces
        let mut target = std::mem::take(&mut self.definitions.interfaces[target_id]);
        let source = &self.definitions.interfaces[source_id];
        let mut checker = SubtypeChecker::new(&self.definitions, &state.packages);

        for (name, source_kind) in &source.exports {
            match target.exports.get(name) {
                Some(target_kind) => {
                    log::debug!(
                        "export `{name}` already exists in target interface {target}",
                        target = target_id.index(),
                    );

                    match (
                        checker
                            .is_subtype(*source_kind, *target_kind)
                            .with_context(|| format!("mismatched type for export `{name}`")),
                        checker
                            .is_subtype(*target_kind, *source_kind)
                            .with_context(|| format!("mismatched type for export `{name}`")),
                    ) {
                        (Ok(_), Ok(_)) => {
                            // The two are compatible, check for remapped type
                            match (*target_kind, *source_kind) {
                                (ItemKind::Type(new), ItemKind::Type(old)) if new != old => {
                                    target.remapped_types.entry(new).or_default().insert(old);
                                }
                                _ => {}
                            }
                        }
                        (Err(e), _) | (_, Err(e)) => {
                            // Neither is a subtype of the other, so error
                            return Err(Error::InstantiationArgMergeFailure {
                                name: name.to_owned(),
                                package: import.package.unwrap().to_string(),
                                kind: "instance".to_string(),
                                span,
                                instantiation: import_span,
                                source: e,
                            });
                        }
                    }
                }
                None => {
                    log::debug!(
                        "adding export `{name}` ({kind}) to interface {target}",
                        kind = source_kind.as_str(&self.definitions),
                        target = target_id.index()
                    );

                    target.exports.insert(name.clone(), *source_kind);
                }
            }
        }

        self.definitions.interfaces[target_id] = target;
        Ok(())
    }

    fn merge_used_types(&mut self, state: &State, target_id: InterfaceId, source_id: InterfaceId) {
        // Temporarily take ownership of the target
        let mut target = std::mem::take(&mut self.definitions.interfaces[target_id]);
        let source = &self.definitions.interfaces[source_id];

        // Merge the source and target usings
        for (name, used) in &source.uses {
            if target.uses.contains_key(name) {
                continue;
            }

            target.uses.insert(name.clone(), used.clone());
        }

        // Remap the usings to point at imported interfaces
        self.remap_uses(state, &mut target.uses);
        self.definitions.interfaces[target_id] = target;
    }

    fn remap_uses(&self, state: &State, uses: &mut IndexMap<String, UsedType>) {
        // Now update all the interface ids in the usings
        for used in uses.values_mut() {
            let old = &self.definitions.interfaces[used.interface];
            let import = &state.imports[old.id.as_deref().unwrap()];
            match &state.current.items[import.item] {
                super::Item::Import(super::Import {
                    kind: ItemKind::Instance(new_id),
                    ..
                }) => {
                    used.interface = *new_id;
                }
                _ => unreachable!(),
            }
        }
    }

    fn named_instantiation_arg(
        &mut self,
        state: &mut State<'a>,
        arg: &'a ast::NamedInstantiationArgument<'a>,
        world: WorldId,
    ) -> ResolutionResult<(String, ItemId, SourceSpan)> {
        let item = self.expr(state, &arg.expr)?;

        let name = match &arg.name {
            ast::InstantiationArgumentName::Ident(ident) => Self::find_matching_interface_name(
                ident.string,
                &self.definitions.worlds[world].imports,
            )
            .unwrap_or(ident.string),
            ast::InstantiationArgumentName::String(name) => name.value,
        };

        Ok((name.to_owned(), item, arg.name.span()))
    }

    fn inferred_instantiation_arg(
        &mut self,
        state: &mut State<'a>,
        ident: &ast::Ident<'a>,
        world: WorldId,
    ) -> ResolutionResult<(String, ItemId, SourceSpan)> {
        let (item_id, item) = state.local_item(ident)?;
        let world = &self.definitions.worlds[world];

        // If the item is an instance with an id, try the id.
        if let ItemKind::Instance(id) = item.kind() {
            if let Some(id) = &self.definitions.interfaces[id].id {
                if world.imports.contains_key(id.as_str()) {
                    return Ok((id.clone(), item_id, ident.span));
                }
            }
        }

        // If the item comes from an import or an alias, try the name associated with it
        match item {
            Item::Import(super::Import { name, .. })
            | Item::Alias(super::Alias { export: name, .. }) => {
                if world.imports.contains_key(name) {
                    return Ok((name.clone(), item_id, ident.span));
                }
            }
            _ => {}
        }

        // Fall back to searching for a matching interface name, provided it is not ambiguous
        // For example, match `foo:bar/baz` if `baz` is the identifier and the only match
        if let Some(name) = Self::find_matching_interface_name(ident.string, &world.imports) {
            return Ok((name.to_owned(), item_id, ident.span));
        }

        // Finally default to the id itself
        Ok((ident.string.to_owned(), item_id, ident.span))
    }

    fn spread_instantiation_arg(
        &mut self,
        state: &mut State<'a>,
        id: &ast::Ident,
        world: WorldId,
        arguments: &mut IndexMap<String, (ItemId, SourceSpan)>,
    ) -> ResolutionResult<()> {
        let item = state.local_item(id)?.0;
        let world = &self.definitions.worlds[world];

        let exports = self.instance_exports(state, item, id.span, InstanceOperation::Spread)?;

        let mut spread = false;
        for name in world.imports.keys() {
            // Check if the argument was already provided
            if arguments.contains_key(name) {
                continue;
            }

            // Alias a matching export of the instance
            if let Some(aliased) = self.alias_export(state, item, exports, name)? {
                spread = true;
                arguments.insert(name.clone(), (aliased, id.span));
            }
        }

        if !spread {
            return Err(Error::SpreadInstantiationNoMatch { span: id.span });
        }

        Ok(())
    }

    fn find_matching_interface_name<'b>(
        name: &str,
        externs: &'b IndexMap<String, ItemKind>,
    ) -> Option<&'b str> {
        // If the given name exists directly, don't treat it as an interface name
        if externs.contains_key(name) {
            return None;
        }

        // Fall back to searching for a matching interface name, provided it is not ambiguous
        // For example, match `foo:bar/baz` if `baz` is the identifier and the only match
        let mut matches = externs.iter().filter(|(n, _)| match n.rfind('/') {
            Some(start) => {
                let mut n = &n[start + 1..];
                if let Some(index) = n.find('@') {
                    n = &n[..index];
                }
                n == name
            }
            None => false,
        });

        let (name, _) = matches.next()?;
        if matches.next().is_some() {
            // More than one match, the name is ambiguous
            return None;
        }

        Some(name)
    }

    fn infer_export_name(&self, state: &'a State, item_id: ItemId) -> Option<&str> {
        let item = &state.current.items[item_id];

        // If the item is an instance with an id, try the id.
        if let ItemKind::Instance(id) = item.kind() {
            if let Some(id) = &self.definitions.interfaces[id].id {
                return Some(id);
            }
        }

        // If the item comes from an import or an alias, try the name associated with it
        match item {
            Item::Import(super::Import { name, .. })
            | Item::Alias(super::Alias { export: name, .. }) => Some(name),
            _ => None,
        }
    }

    fn postfix_expr(
        &mut self,
        state: &mut State<'a>,
        item: ItemId,
        expr: &ast::PostfixExpr<'a>,
        parent_span: SourceSpan,
    ) -> ResolutionResult<ItemId> {
        let exports = self.instance_exports(state, item, parent_span, InstanceOperation::Access)?;

        match expr {
            ast::PostfixExpr::Access(expr) => {
                let name = Self::find_matching_interface_name(expr.id.string, exports)
                    .unwrap_or(expr.id.string);

                self.alias_export(state, item, exports, name)?
                    .ok_or_else(|| Error::MissingInstanceExport {
                        name: name.to_owned(),
                        span: expr.span,
                    })
            }
            ast::PostfixExpr::NamedAccess(expr) => self
                .alias_export(state, item, exports, expr.string.value)?
                .ok_or_else(|| Error::MissingInstanceExport {
                    name: expr.string.value.to_owned(),
                    span: expr.span,
                }),
        }
    }

    fn instance_exports(
        &self,
        state: &State,
        item: ItemId,
        span: SourceSpan,
        operation: InstanceOperation,
    ) -> ResolutionResult<&IndexMap<String, ItemKind>> {
        match state.current.items[item].kind() {
            ItemKind::Instance(id) => Ok(&self.definitions.interfaces[id].exports),
            ItemKind::Instantiation(id) => {
                Ok(&self.definitions.worlds[state.packages[id].world].exports)
            }
            kind => Err(Error::NotAnInstance {
                kind: kind.as_str(&self.definitions).to_string(),
                operation,
                span,
            }),
        }
    }

    fn alias_export(
        &self,
        state: &mut State<'a>,
        item: ItemId,
        exports: &IndexMap<String, ItemKind>,
        name: &str,
    ) -> ResolutionResult<Option<ItemId>> {
        let kind = match exports.get(name) {
            Some(kind) => *kind,
            None => return Ok(None),
        };

        let aliases = state.aliases.entry(item).or_default();
        if let Some(id) = aliases.get(name) {
            return Ok(Some(*id));
        }

        let id = state.current.items.alloc(Item::Alias(super::Alias {
            item,
            export: name.to_owned(),
            kind,
        }));

        aliases.insert(name.to_owned(), id);
        Ok(Some(id))
    }

    fn validate_target(
        &self,
        state: &State,
        path: &ast::PackagePath,
        world: WorldId,
    ) -> ResolutionResult<()> {
        let world = &self.definitions.worlds[world];

        let mut checker = SubtypeChecker::new(&self.definitions, &state.packages);

        // The output is allowed to import a subset of the world's imports
        checker.invert();
        for (name, import) in &state.imports {
            let expected = world
                .imports
                .get(name)
                .ok_or_else(|| Error::ImportNotInTarget {
                    name: name.clone(),
                    world: path.string.to_owned(),
                    span: import.span,
                })?;

            checker
                .is_subtype(
                    expected.promote(),
                    state.root_scope().items[import.item].kind(),
                )
                .map_err(|e| Error::TargetMismatch {
                    kind: ExternKind::Import,
                    name: name.clone(),
                    world: path.string.to_owned(),
                    span: import.span,
                    source: e,
                })?;
        }

        checker.revert();

        // The output must export every export in the world
        for (name, expected) in &world.exports {
            let export = state
                .exports
                .get(name)
                .ok_or_else(|| Error::MissingTargetExport {
                    name: name.clone(),
                    world: path.string.to_owned(),
                    kind: expected.as_str(&self.definitions).to_string(),
                    span: path.span,
                })?;

            checker
                .is_subtype(
                    state.root_scope().items[export.item].kind(),
                    expected.promote(),
                )
                .map_err(|e| Error::TargetMismatch {
                    kind: ExternKind::Export,
                    name: name.clone(),
                    world: path.string.to_owned(),
                    span: export.span,
                    source: e,
                })?;
        }

        Ok(())
    }
}
