//! Module for resolving WAC documents.

use self::package::Package;
use crate::ast::{self, new_error_with_span};
use anyhow::{bail, Context, Result};
use id_arena::{Arena, Id};
use indexmap::{IndexMap, IndexSet};
use pest::{Position, Span};
use serde::{Serialize, Serializer};
use std::{
    borrow::Cow,
    collections::{hash_map, HashMap},
    fmt, fs,
    path::{Path, PathBuf},
};
use wit_parser::Resolve;

mod package;
mod types;

pub use types::*;

fn serialize_arena<T, S>(arena: &Arena<T>, serializer: S) -> std::result::Result<S::Ok, S::Error>
where
    S: Serializer,
    T: Serialize,
{
    use serde::ser::SerializeSeq;

    let mut s = serializer.serialize_seq(Some(arena.len()))?;
    for (_, e) in arena.iter() {
        s.serialize_element(e)?;
    }

    s.end()
}

fn serialize_id_map<T, S>(
    map: &IndexMap<String, Id<T>>,
    serializer: S,
) -> std::result::Result<S::Ok, S::Error>
where
    S: Serializer,
    T: Serialize,
{
    use serde::ser::SerializeMap;

    let mut s = serializer.serialize_map(Some(map.len()))?;
    for (k, v) in map {
        s.serialize_entry(k, &v.index())?;
    }

    s.end()
}

fn serialize_id<T, S>(id: &Id<T>, serializer: S) -> std::result::Result<S::Ok, S::Error>
where
    S: Serializer,
    T: Serialize,
{
    id.index().serialize(serializer)
}

fn serialize_optional_id<T, S>(
    id: &Option<Id<T>>,
    serializer: S,
) -> std::result::Result<S::Ok, S::Error>
where
    S: Serializer,
    T: Serialize,
{
    match id {
        Some(i) => serializer.serialize_some(&i.index()),
        None => serializer.serialize_none(),
    }
}

/// A trait implemented by package resolvers.
///
/// This is used when resolving a document to resolve any referenced packages.
pub trait PackageResolver {
    /// Resolves a package name to the package bytes.
    ///
    /// Returns `Ok(None)` if the package could not be found.
    fn resolve(&self, name: &ast::PackageName) -> Result<Option<Vec<u8>>>;
}

/// Used to resolve packages from the file system.
pub struct FileSystemPackageResolver {
    root: PathBuf,
    overrides: HashMap<String, PathBuf>,
}

impl FileSystemPackageResolver {
    /// Creates a new `FileSystemPackageResolver` with the given root directory.
    pub fn new(root: impl Into<PathBuf>, overrides: HashMap<String, PathBuf>) -> Self {
        Self {
            root: root.into(),
            overrides,
        }
    }
}

impl Default for FileSystemPackageResolver {
    fn default() -> Self {
        Self::new("deps", Default::default())
    }
}

impl PackageResolver for FileSystemPackageResolver {
    fn resolve(&self, name: &ast::PackageName) -> Result<Option<Vec<u8>>> {
        let path = if let Some(path) = self.overrides.get(name.as_str()) {
            if !path.exists() {
                bail!(
                    "local path `{path}` for package `{name}` does not exist",
                    path = path.display(),
                    name = name.as_str()
                )
            }

            path.clone()
        } else {
            let mut path = self.root.clone();
            for part in &name.parts {
                path.push(part.as_str());
            }

            // If the path is not a directory, use a `.wasm` or `.wat` extension
            if !path.is_dir() {
                path.set_extension("wasm");

                #[cfg(feature = "wat")]
                {
                    path.set_extension("wat");
                    if !path.exists() {
                        path.set_extension("wasm");
                    }
                }
            }

            path
        };

        // First check to see if a directory exists.
        // If so, then treat it as a textual WIT package.
        if path.is_dir() {
            log::debug!(
                "loading WIT package from directory `{path}`",
                path = path.display()
            );

            let mut resolve = Resolve::new();
            let (pkg, _) = resolve.push_dir(&path)?;

            return wit_component::encode(Some(true), &resolve, pkg)
                .with_context(|| {
                    format!(
                        "failed to encode WIT package from directory `{path}`",
                        path = path.display()
                    )
                })
                .map(Some);
        }

        if !path.is_file() {
            log::debug!("package `{path}` does not exist", path = path.display());
            return Ok(None);
        }

        log::debug!("loading package from `{path}`", path = path.display());
        let bytes = fs::read(&path)
            .with_context(|| format!("failed to read package `{path}`", path = path.display()))?;

        #[cfg(feature = "wat")]
        if path.extension().and_then(std::ffi::OsStr::to_str) == Some("wat") {
            let bytes = match wat::parse_bytes(&bytes) {
                Ok(std::borrow::Cow::Borrowed(_)) => bytes,
                Ok(std::borrow::Cow::Owned(wat)) => wat,
                Err(mut e) => {
                    e.set_path(path);
                    bail!(e);
                }
            };

            return Ok(Some(bytes));
        }

        Ok(Some(bytes))
    }
}

/// Represents the kind of an item.
#[derive(Debug, Clone, Copy, Serialize, Hash, Eq, PartialEq)]
#[serde(rename_all = "camelCase")]
pub enum ItemKind {
    /// The kind is a type.
    Type(Type),
    /// The kind is a function.
    Func(#[serde(serialize_with = "serialize_id")] FuncId),
    /// The kind is a component instance.
    Instance(#[serde(serialize_with = "serialize_id")] InterfaceId),
    /// The kind is an instantiation of a component.
    Instantiation(#[serde(serialize_with = "serialize_id")] WorldId),
    /// The kind is a component.
    Component(#[serde(serialize_with = "serialize_id")] WorldId),
    /// The kind is a core module.
    Module(#[serde(serialize_with = "serialize_id")] ModuleId),
    /// The kind is a value.
    Value(ValueType),
}

impl ItemKind {
    pub(crate) fn display<'a>(&'a self, definitions: &'a Definitions) -> impl fmt::Display + 'a {
        ItemKindDisplay {
            kind: *self,
            definitions,
        }
    }
}

struct ItemKindDisplay<'a> {
    kind: ItemKind,
    definitions: &'a Definitions,
}

impl fmt::Display for ItemKindDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.kind {
            ItemKind::Func(_) => write!(f, "function"),
            ItemKind::Type(ty) => ty.display(self.definitions).fmt(f),
            ItemKind::Instance(_) | ItemKind::Instantiation(_) => write!(f, "instance"),
            ItemKind::Component(_) => write!(f, "component"),
            ItemKind::Module(_) => write!(f, "module"),
            ItemKind::Value(_) => write!(f, "value"),
        }
    }
}

/// Represents the source of an item.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum ItemSource {
    /// The item comes from a local definition.
    Definition,
    /// The item comes from a use statement.
    Use,
    /// The item comes from an import,
    Import {
        /// The import string to use.
        with: Option<String>,
    },
    /// The item comes from an alias.
    Alias {
        /// The instance being aliased.
        #[serde(serialize_with = "serialize_id")]
        item: ItemId,
        /// The export name.
        export: String,
    },
    /// The item comes from an instantiation.
    Instantiation {
        /// The arguments of the instantiation.
        #[serde(serialize_with = "serialize_id_map")]
        arguments: IndexMap<String, ItemId>,
    },
}

/// Represents an item in a resolved document.
#[derive(Debug, Clone, Serialize)]
pub struct Item {
    /// The kind of the item.
    pub kind: ItemKind,
    /// The source of the item.
    pub source: ItemSource,
}

/// Represents an identifier for an item.
pub type ItemId = Id<Item>;

/// An identifier for scopes.
pub type ScopeId = Id<Scope>;

/// Represents a scope for named items.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Scope {
    #[serde(serialize_with = "serialize_optional_id")]
    parent: Option<ScopeId>,
    #[serde(serialize_with = "serialize_id_map")]
    items: IndexMap<String, ItemId>,
}

impl Scope {
    /// Gets a named item from the scope.
    pub fn get(&self, name: &str) -> Option<ItemId> {
        self.items.get(name).copied()
    }

    /// Iterates all named items in the scope.
    pub fn iter(&self) -> impl Iterator<Item = ItemId> + '_ {
        self.items.values().copied()
    }
}

struct ResolutionState<'a> {
    document: &'a ast::Document<'a>,
    resolver: Option<Box<dyn PackageResolver>>,
    root_scope: ScopeId,
    current_scope: ScopeId,
    packages: HashMap<String, Package>,
    offsets: HashMap<ItemId, usize>,
    aliases: HashMap<(ItemId, String), ItemId>,
}

/// Represents a kind of function in the component model.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum FuncKind {
    /// The function is a "free" function (i.e. not associated with a resource).
    Free,
    /// The function is a method on a resource.
    Method,
    /// The function is a static method on a resource.
    Static,
    /// The function is a resource constructor.
    Constructor,
}

impl fmt::Display for FuncKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            FuncKind::Free => write!(f, "function"),
            FuncKind::Method => write!(f, "method"),
            FuncKind::Static => write!(f, "static method"),
            FuncKind::Constructor => write!(f, "constructor"),
        }
    }
}

/// Represents a resolved document.
///
/// A resolution may be encoded to a WebAssembly component.
#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ResolvedDocument {
    /// The name of the package being resolved.
    pub package: String,
    /// The definitions in the resolution.
    pub definitions: Definitions,
    /// The items in the resolution.
    #[serde(serialize_with = "serialize_arena")]
    pub items: Arena<Item>,
    /// The name scopes in the resolution.
    #[serde(serialize_with = "serialize_arena")]
    pub scopes: Arena<Scope>,
}

impl ResolvedDocument {
    /// Creates a new resolved document from the given document.
    pub fn new(
        document: &ast::Document,
        package: impl Into<String>,
        resolver: Option<Box<dyn PackageResolver>>,
    ) -> Result<Self> {
        let mut scopes = Arena::new();
        let root_scope = scopes.alloc(Scope {
            parent: None,
            items: Default::default(),
        });

        let mut resolution = ResolvedDocument {
            package: package.into(),
            definitions: Default::default(),
            items: Default::default(),
            scopes,
        };

        let mut state = ResolutionState {
            document,
            resolver,
            root_scope,
            current_scope: root_scope,
            packages: Default::default(),
            offsets: Default::default(),
            aliases: Default::default(),
        };

        for stmt in &document.statements {
            match &stmt.stmt {
                ast::Statement::Import(i) => resolution.import(&mut state, i)?,
                ast::Statement::Type(t) => resolution.type_statement(&mut state, t)?,
                ast::Statement::Let(l) => resolution.let_statement(&mut state, l)?,
                ast::Statement::Export(_) => todo!("implement export statements"),
            }
        }

        Ok(resolution)
    }

    /// Encode the resolved document as a WebAssembly component.
    pub fn encode(&self) -> Result<Vec<u8>> {
        todo!("implement encoding")
    }

    fn get(&self, state: &ResolutionState, id: &ast::Ident) -> Option<ItemId> {
        let mut current = &self.scopes[state.current_scope];
        loop {
            if let Some(item) = current.get(id.as_str()) {
                return Some(item);
            }

            current = &self.scopes[current.parent?];
        }
    }

    fn require(&self, state: &ResolutionState, id: &ast::Ident) -> Result<ItemId> {
        self.get(state, id).ok_or_else(|| {
            new_error_with_span(
                state.document.path,
                id.0,
                format!("undefined name `{id}`", id = id.as_str()),
            )
        })
    }

    fn push_scope(&mut self, state: &mut ResolutionState) {
        state.current_scope = self.scopes.alloc(Scope {
            parent: Some(state.current_scope),
            items: Default::default(),
        });
    }

    fn pop_scope(&mut self, state: &mut ResolutionState) -> ScopeId {
        let id = state.current_scope;
        state.current_scope = self.scopes[state.current_scope]
            .parent
            .expect("expected a scope to pop");
        id
    }

    fn register_name(
        &mut self,
        state: &mut ResolutionState,
        id: ast::Ident,
        item: ItemId,
    ) -> Result<()> {
        if let Some(prev) = self.scopes[state.current_scope]
            .items
            .insert(id.as_str().to_owned(), item)
        {
            let offset = state.offsets[&prev];
            let (line, column) = Position::new(id.0.get_input(), offset).unwrap().line_col();
            return Err(new_error_with_span(
                state.document.path,
                id.0,
                format!(
                    "`{id}` was previously defined at {path}:{line}:{column}",
                    id = id.as_str(),
                    path = state.document.path.display(),
                ),
            ));
        }

        state.offsets.insert(item, id.0.start());

        Ok(())
    }

    fn import(&mut self, state: &mut ResolutionState, stmt: &ast::ImportStatement) -> Result<()> {
        let kind = match &stmt.ty {
            ast::ImportType::Package(p) => self.resolve_package_export(state, p)?,
            ast::ImportType::Func(ty) => ItemKind::Func(self.func_type(
                state,
                &ty.params,
                ty.results.as_ref(),
                FuncKind::Free,
            )?),
            ast::ImportType::Interface(i) => self.inline_interface(state, i)?,
            ast::ImportType::Ident(id) => self.items[self.require(state, id)?].kind,
        };

        // Promote function types, instance types, and component types to functions, instances, and components
        let kind = match kind {
            ItemKind::Type(Type::Func(id)) => ItemKind::Func(id),
            ItemKind::Type(Type::Interface(id)) => ItemKind::Instance(id),
            ItemKind::Type(Type::World(id)) => ItemKind::Component(id),
            _ => kind,
        };

        let id = self.items.alloc(Item {
            kind,
            source: ItemSource::Import {
                with: stmt.with.as_ref().map(|w| w.name.as_str().to_owned()),
            },
        });

        self.register_name(state, stmt.id, id)
    }

    fn type_statement(
        &mut self,
        state: &mut ResolutionState,
        stmt: &ast::TypeStatement,
    ) -> Result<()> {
        match stmt {
            ast::TypeStatement::Interface(i) => self.interface_decl(state, i),
            ast::TypeStatement::World(w) => self.world_decl(state, w),
            ast::TypeStatement::Type(t) => self.type_decl(state, t).map(|_| ()),
        }
    }

    fn let_statement<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        stmt: &'a ast::LetStatement,
    ) -> Result<()> {
        let item = self.expr(state, &stmt.expr)?;
        self.register_name(state, stmt.id, item)
    }

    fn inline_interface(
        &mut self,
        state: &mut ResolutionState,
        iface: &ast::InlineInterface,
    ) -> Result<ItemKind> {
        self.push_scope(state);

        let mut ty = Interface {
            id: None,
            exports: Default::default(),
            scope: Some(state.current_scope),
        };

        self.interface_body(state, None, &iface.body, &mut ty)?;

        self.pop_scope(state);

        Ok(ItemKind::Type(Type::Interface(
            self.definitions.interfaces.alloc(ty),
        )))
    }

    fn interface_decl(
        &mut self,
        state: &mut ResolutionState,
        decl: &ast::InterfaceDecl,
    ) -> Result<()> {
        self.push_scope(state);

        let mut ty = Interface {
            id: Some(format!(
                "{pkg}/{iface}",
                pkg = self.package,
                iface = decl.id
            )),
            exports: Default::default(),
            scope: Some(state.current_scope),
        };

        self.interface_body(state, Some(decl.id.as_str()), &decl.body, &mut ty)?;

        self.pop_scope(state);

        let ty = self.definitions.interfaces.alloc(ty);

        let id = self.items.alloc(Item {
            kind: ItemKind::Type(Type::Interface(ty)),
            source: ItemSource::Definition,
        });

        self.register_name(state, decl.id, id)
    }

    fn world_decl(&mut self, state: &mut ResolutionState, decl: &ast::WorldDecl) -> Result<()> {
        self.push_scope(state);

        let mut ty = World {
            imports: Default::default(),
            exports: Default::default(),
            scope: Some(state.current_scope),
        };

        self.world_body(state, decl.id.as_str(), &decl.body, &mut ty)?;

        self.pop_scope(state);

        let ty = self.definitions.worlds.alloc(ty);

        let id = self.items.alloc(Item {
            kind: ItemKind::Type(Type::World(ty)),
            source: ItemSource::Definition,
        });

        self.register_name(state, decl.id, id)
    }

    fn interface_body(
        &mut self,
        state: &mut ResolutionState,
        name: Option<&str>,
        body: &ast::InterfaceBody,
        ty: &mut Interface,
    ) -> Result<()> {
        for item in &body.items {
            match &item.stmt {
                ast::InterfaceItemStatement::Use(u) => {
                    self.use_type(state, u, &mut ty.exports, false)?
                }
                ast::InterfaceItemStatement::Type(decl) => {
                    let kind = self.type_decl(state, decl)?;
                    let prev = ty
                        .exports
                        .insert(decl.id().as_str().into(), Extern::Kind(kind));
                    assert!(prev.is_none(), "duplicate type in scope");
                }
                ast::InterfaceItemStatement::Export(e) => {
                    let kind = ItemKind::Func(self.func_type_ref(state, &e.ty, FuncKind::Free)?);
                    if ty
                        .exports
                        .insert(e.id.as_str().into(), Extern::Kind(kind))
                        .is_some()
                    {
                        return Err(new_error_with_span(
                            state.document.path,
                            e.id.0,
                            match name {
                                Some(name) => format!(
                                    "duplicate interface export `{id}` for interface `{name}`",
                                    id = e.id.as_str()
                                ),
                                None => {
                                    format!("duplicate interface export `{id}`", id = e.id.as_str())
                                }
                            },
                        ));
                    }
                }
            }
        }

        Ok(())
    }

    fn world_body(
        &mut self,
        state: &mut ResolutionState,
        world: &str,
        body: &ast::WorldBody,
        ty: &mut World,
    ) -> Result<()> {
        let mut includes = Vec::new();
        for item in &body.items {
            match &item.stmt {
                ast::WorldItemStatement::Use(u) => {
                    self.use_type(state, u, &mut ty.imports, true)?
                }
                ast::WorldItemStatement::Type(decl) => {
                    let kind = self.type_decl(state, decl)?;
                    let prev = ty
                        .exports
                        .insert(decl.id().as_str().into(), Extern::Kind(kind));
                    assert!(prev.is_none(), "duplicate type in scope");
                }
                ast::WorldItemStatement::Import(i) => {
                    self.world_item_decl(state, &i.decl, true, world, ty)?
                }
                ast::WorldItemStatement::Export(e) => {
                    self.world_item_decl(state, &e.decl, false, world, ty)?
                }
                ast::WorldItemStatement::Include(i) => {
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

    fn world_item_decl(
        &mut self,
        state: &mut ResolutionState,
        decl: &ast::WorldItemDecl,
        import: bool,
        world: &str,
        ty: &mut World,
    ) -> Result<()> {
        let check_name = |name: &str, span: Span, ty: &World| {
            let exists: bool = if import {
                ty.imports.contains_key(name)
            } else {
                ty.exports.contains_key(name)
            };
            if exists {
                return Err(new_error_with_span(
                    state.document.path,
                    span,
                    format!(
                        "{dir} `{name}` conflicts with existing {dir} of the same name in world `{world}`",
                        dir = if import { "import" } else { "export" },
                    ),
                ));
            }

            Ok(())
        };

        let (name, kind) = match decl {
            ast::WorldItemDecl::Named(named) => {
                check_name(named.id.as_str(), named.id.0, ty)?;

                (
                    named.id.as_str().into(),
                    match &named.ty {
                        ast::ExternType::Ident(id) => {
                            let item = &self.items[self.require(state, id)?];
                            match item.kind {
                                ItemKind::Type(Type::Interface(id)) | ItemKind::Instance(id) => {
                                    ItemKind::Instance(id)
                                }
                                ItemKind::Type(Type::Func(id)) | ItemKind::Func(id) => {
                                    ItemKind::Func(id)
                                }
                                _ => {
                                    return Err(new_error_with_span(
                                        state.document.path,
                                        id.0,
                                        format!(
                                            "`{id}` ({kind}) is not a function type or interface",
                                            kind = item.kind.display(&self.definitions),
                                            id = id.as_str(),
                                        ),
                                    ))
                                }
                            }
                        }
                        ast::ExternType::Func(f) => ItemKind::Func(self.func_type(
                            state,
                            &f.params,
                            f.results.as_ref(),
                            FuncKind::Free,
                        )?),
                        ast::ExternType::Interface(i) => self.inline_interface(state, i)?,
                    },
                )
            }
            ast::WorldItemDecl::Interface(i) => match i {
                ast::InterfaceRef::Ident(id) => {
                    let item = &self.items[self.require(state, id)?];
                    match item.kind {
                        ItemKind::Type(Type::Interface(iface_ty_id))
                        | ItemKind::Instance(iface_ty_id) => {
                            let iface_id = self.definitions.interfaces[iface_ty_id]
                                .id
                                .as_ref()
                                .expect("expected an interface id");
                            check_name(iface_id, id.0, ty)?;
                            (iface_id.clone(), ItemKind::Instance(iface_ty_id))
                        }
                        _ => {
                            return Err(new_error_with_span(
                                state.document.path,
                                id.0,
                                format!(
                                    "`{id}` ({kind}) is not an interface",
                                    kind = item.kind.display(&self.definitions),
                                    id = id.as_str()
                                ),
                            ))
                        }
                    }
                }
                ast::InterfaceRef::Path(p) => match self.resolve_package_export(state, p)? {
                    ItemKind::Type(Type::Interface(id)) | ItemKind::Instance(id) => {
                        let name = self.definitions.interfaces[id]
                            .id
                            .as_ref()
                            .expect("expected an interface id");
                        check_name(name, p.span(), ty)?;
                        (name.clone(), ItemKind::Instance(id))
                    }
                    kind => {
                        return Err(new_error_with_span(
                            state.document.path,
                            p.span(),
                            format!(
                                "`{path}` ({kind}) is not an interface",
                                path = p.as_str(),
                                kind = kind.display(&self.definitions)
                            ),
                        ))
                    }
                },
            },
        };

        if import {
            ty.imports.insert(name, Extern::Kind(kind));
        } else {
            ty.exports.insert(name, Extern::Kind(kind));
        }

        Ok(())
    }

    fn world_include(
        &mut self,
        state: &mut ResolutionState,
        stmt: &ast::WorldIncludeStatement,
        world: &str,
        ty: &mut World,
    ) -> Result<()> {
        let mut replacements = HashMap::new();
        for item in stmt
            .with
            .as_ref()
            .map(|w| w.names.as_slice())
            .unwrap_or(&[])
        {
            let prev = replacements.insert(item.name.as_str(), item);
            if prev.is_some() {
                return Err(new_error_with_span(
                    state.document.path,
                    item.name.0,
                    format!(
                        "duplicate `{name}` in world include `with` clause",
                        name = item.name,
                    ),
                ));
            }
        }

        let id = match &stmt.world {
            ast::WorldRef::Ident(id) => {
                let item = &self.items[self.require(state, id)?];
                match item.kind {
                    ItemKind::Type(Type::World(id)) | ItemKind::Component(id) => id,
                    kind => {
                        return Err(new_error_with_span(
                            state.document.path,
                            id.0,
                            format!(
                                "`{id}` ({kind}) is not a world",
                                id = id.as_str(),
                                kind = kind.display(&self.definitions)
                            ),
                        ))
                    }
                }
            }
            ast::WorldRef::Path(path) => match self.resolve_package_export(state, path)? {
                ItemKind::Type(Type::World(id)) | ItemKind::Component(id) => id,
                kind => {
                    return Err(new_error_with_span(
                        state.document.path,
                        path.span(),
                        format!(
                            "`{path}` ({kind}) is not a world",
                            path = path.as_str(),
                            kind = kind.display(&self.definitions)
                        ),
                    ))
                }
            },
        };

        let other = &self.definitions.worlds[id];
        for (name, item) in &other.imports {
            let name = replace_name(
                stmt,
                world,
                ty,
                name,
                true,
                &mut replacements,
                state.document.path,
            )?;
            ty.imports.entry(name).or_insert(*item);
        }

        for (name, item) in &other.exports {
            let name = replace_name(
                stmt,
                world,
                ty,
                name,
                false,
                &mut replacements,
                state.document.path,
            )?;
            ty.exports.entry(name).or_insert(*item);
        }

        if let Some(missing) = replacements.values().next() {
            return Err(new_error_with_span(
                state.document.path,
                missing.name.0,
                format!(
                    "world `{other}` does not have an import or export with kebab-name `{name}`",
                    other = stmt.world.name(),
                    name = missing.name.as_str(),
                ),
            ));
        }

        return Ok(());

        fn replace_name(
            stmt: &ast::WorldIncludeStatement,
            world: &str,
            ty: &mut World,
            name: &str,
            import: bool,
            replacements: &mut HashMap<&str, &ast::WorldIncludeItem>,
            path: &Path,
        ) -> Result<String> {
            // Check for a id, which doesn't get replaced.
            if name.contains(':') {
                return Ok(name.to_owned());
            }

            let (name, span) = replacements
                .remove(name)
                .map(|r| (r.other.as_str(), r.other.0))
                .unwrap_or_else(|| (name, stmt.world.span()));

            let exists = if import {
                ty.imports.contains_key(name)
            } else {
                ty.exports.contains_key(name)
            };

            if exists {
                return Err(new_error_with_span(
                    path,
                    span,
                    format!(
                        "{dir} `{name}` from world `{other}` conflicts with {dir} of the same name in world `{world}`{hint}",
                        dir = if import { "import" } else { "export" },
                        other = stmt.world.name(),
                        hint = if stmt.with.is_some() { "" } else {
                            " (consider using a `with` clause to use a different name)"
                        }
                    ),
                ));
            }

            Ok(name.to_owned())
        }
    }

    fn use_type(
        &mut self,
        state: &mut ResolutionState,
        stmt: &ast::UseStatement,
        externs: &mut ExternMap,
        in_world: bool,
    ) -> Result<()> {
        let (interface, name) = match &stmt.items.path {
            ast::UsePath::Package(path) => match self.resolve_package_export(state, path)? {
                ItemKind::Type(Type::Interface(id)) | ItemKind::Instance(id) => (id, path.as_str()),
                kind => {
                    return Err(new_error_with_span(
                        state.document.path,
                        path.span(),
                        format!(
                            "`{path}` ({kind}) is not an interface",
                            path = path.as_str(),
                            kind = kind.display(&self.definitions)
                        ),
                    ))
                }
            },
            ast::UsePath::Ident(id) => {
                let item = &self.items[self.require(state, id)?];
                match item.kind {
                    ItemKind::Type(Type::Interface(iface_ty_id))
                    | ItemKind::Instance(iface_ty_id) => (iface_ty_id, id.as_str()),
                    kind => {
                        return Err(new_error_with_span(
                            state.document.path,
                            id.0,
                            format!(
                                "`{id}` ({kind}) is not an interface",
                                id = id.as_str(),
                                kind = kind.display(&self.definitions)
                            ),
                        ))
                    }
                }
            }
        };

        for item in &stmt.items.list {
            let ident = item.as_clause.as_ref().map(|c| c.id).unwrap_or(item.id);
            let (index, _, ext) = self.definitions.interfaces[interface]
                .exports
                .get_full(item.id.as_str())
                .ok_or_else(|| {
                    new_error_with_span(
                        state.document.path,
                        item.id.0,
                        format!(
                            "type `{item}` is not defined in interface `{name}`",
                            item = item.id.as_str()
                        ),
                    )
                })?;

            let kind = ext.kind();
            match kind {
                ItemKind::Type(Type::Value(ty)) => {
                    let new_extern = Extern::Use {
                        interface,
                        export_index: index,
                        ty,
                    };

                    if in_world {
                        // A `use` of a type in a world will (transitively) import the interface that defines
                        // the type being used. This walks up the use chain, adding any necessary imports of
                        // the interfaces.
                        let mut cur = new_extern;
                        while let Extern::Use {
                            interface,
                            export_index,
                            ..
                        } = cur
                        {
                            let iface = &self.definitions.interfaces[interface];
                            let id = iface.id.as_deref().expect("interface must have an id");

                            if !externs.contains_key(id) {
                                externs.insert(
                                    id.to_owned(),
                                    Extern::Kind(ItemKind::Instance(interface)),
                                );
                            }

                            cur = iface.exports[export_index];
                        }
                    }

                    externs.insert(ident.as_str().into(), new_extern);

                    let id = self.items.alloc(Item {
                        kind,
                        source: ItemSource::Use,
                    });
                    self.register_name(state, ident, id)?;
                }
                _ => {
                    return Err(new_error_with_span(
                        state.document.path,
                        item.id.0,
                        format!(
                            "`{item}` ({kind}) is not a value type in interface `{name}`",
                            kind = kind.display(&self.definitions),
                            item = item.id.as_str()
                        ),
                    ));
                }
            }
        }

        Ok(())
    }

    fn type_decl(&mut self, state: &mut ResolutionState, decl: &ast::TypeDecl) -> Result<ItemKind> {
        match decl {
            ast::TypeDecl::Resource(r) => self.resource_decl(state, r),
            ast::TypeDecl::Variant(v) => self.variant_decl(state, v),
            ast::TypeDecl::Record(r) => self.record_decl(state, r),
            ast::TypeDecl::Flags(f) => self.flags_decl(state, f),
            ast::TypeDecl::Enum(e) => self.enum_decl(state, e),
            ast::TypeDecl::Alias(a) => self.type_alias(state, a),
        }
    }

    fn resource_decl(
        &mut self,
        state: &mut ResolutionState,
        decl: &ast::ResourceDecl,
    ) -> Result<ItemKind> {
        // Resources are allowed to be self-referential, so we need to allocate the resource
        // before we resolve the methods.
        let id = self.definitions.resources.alloc(Resource {
            methods: Default::default(),
        });
        let kind = ItemKind::Type(Type::Value(
            self.definitions.types.alloc(DefinedType::Resource(id)),
        ));
        let item_id = self.items.alloc(Item {
            kind,
            source: ItemSource::Definition,
        });

        self.register_name(state, decl.id, item_id)?;

        self.definitions.resources[id].methods = match &decl.body {
            ast::ResourceBody::Empty(_) => Default::default(),
            ast::ResourceBody::Methods { methods, .. } => {
                let mut resource_methods = IndexMap::new();
                for (method, _) in methods.iter() {
                    let (name, method, span) = match method {
                        ast::ResourceMethod::Constructor(ast::Constructor { keyword, params }) => (
                            String::new(),
                            ResourceMethod {
                                kind: FuncKind::Constructor,
                                ty: self.func_type(state, params, None, FuncKind::Constructor)?,
                            },
                            keyword.0,
                        ),
                        ast::ResourceMethod::Method(ast::Method {
                            id, func, keyword, ..
                        }) => (
                            id.as_str().into(),
                            ResourceMethod {
                                kind: if keyword.is_some() {
                                    FuncKind::Static
                                } else {
                                    FuncKind::Method
                                },
                                ty: self.func_type_ref(state, func, FuncKind::Method)?,
                            },
                            id.0,
                        ),
                    };

                    let prev = resource_methods.insert(name.clone(), method);
                    if prev.is_some() {
                        return Err(new_error_with_span(
                            state.document.path,
                            span,
                            if name.is_empty() {
                                format!(
                                    "duplicate constructor for resource `{res}`",
                                    res = decl.id.as_str()
                                )
                            } else {
                                format!(
                                    "duplicate method `{name}` for resource `{res}`",
                                    res = decl.id.as_str()
                                )
                            },
                        ));
                    }
                }

                resource_methods
            }
        };

        Ok(kind)
    }

    fn variant_decl(
        &mut self,
        state: &mut ResolutionState,
        decl: &ast::VariantDecl,
    ) -> Result<ItemKind> {
        let mut cases = IndexMap::new();
        for case in &decl.body.cases {
            if cases
                .insert(
                    case.id.as_str().into(),
                    case.ty
                        .as_ref()
                        .map(|t| self.ty(state, &t.ty))
                        .transpose()?,
                )
                .is_some()
            {
                return Err(new_error_with_span(
                    state.document.path,
                    case.id.0,
                    format!(
                        "duplicate case `{case}` for variant type `{ty}`",
                        case = case.id,
                        ty = decl.id
                    ),
                ));
            }
        }

        let kind = ItemKind::Type(Type::Value(
            self.definitions
                .types
                .alloc(DefinedType::Variant(Variant { cases })),
        ));
        let id = self.items.alloc(Item {
            kind,
            source: ItemSource::Definition,
        });
        self.register_name(state, decl.id, id)?;
        Ok(kind)
    }

    fn record_decl(
        &mut self,
        state: &mut ResolutionState,
        decl: &ast::RecordDecl,
    ) -> Result<ItemKind> {
        let mut fields = IndexMap::new();
        for field in &decl.body.fields {
            if fields
                .insert(field.id.as_str().into(), self.ty(state, &field.ty)?)
                .is_some()
            {
                return Err(new_error_with_span(
                    state.document.path,
                    field.id.0,
                    format!(
                        "duplicate field `{field}` for record type `{ty}`",
                        field = field.id,
                        ty = decl.id
                    ),
                ));
            }
        }

        let kind = ItemKind::Type(Type::Value(
            self.definitions
                .types
                .alloc(DefinedType::Record(Record { fields })),
        ));
        let id = self.items.alloc(Item {
            kind,
            source: ItemSource::Definition,
        });
        self.register_name(state, decl.id, id)?;
        Ok(kind)
    }

    fn flags_decl(
        &mut self,
        state: &mut ResolutionState,
        decl: &ast::FlagsDecl,
    ) -> Result<ItemKind> {
        let mut flags = IndexSet::new();
        for flag in &decl.body.flags {
            if !flags.insert(flag.as_str().into()) {
                return Err(new_error_with_span(
                    state.document.path,
                    flag.0,
                    format!(
                        "duplicate flag `{flag}` for flags type `{ty}`",
                        ty = decl.id
                    ),
                ));
            }
        }

        let kind = ItemKind::Type(Type::Value(
            self.definitions
                .types
                .alloc(DefinedType::Flags(Flags(flags))),
        ));
        let id = self.items.alloc(Item {
            kind,
            source: ItemSource::Definition,
        });
        self.register_name(state, decl.id, id)?;
        Ok(kind)
    }

    fn enum_decl(&mut self, state: &mut ResolutionState, decl: &ast::EnumDecl) -> Result<ItemKind> {
        let mut cases = IndexSet::new();
        for case in &decl.body.cases {
            if !cases.insert(case.as_str().into()) {
                return Err(new_error_with_span(
                    state.document.path,
                    case.0,
                    format!("duplicate case `{case}` for enum type `{ty}`", ty = decl.id),
                ));
            }
        }

        let kind = ItemKind::Type(Type::Value(
            self.definitions.types.alloc(DefinedType::Enum(Enum(cases))),
        ));
        let id = self.items.alloc(Item {
            kind,
            source: ItemSource::Definition,
        });
        self.register_name(state, decl.id, id)?;
        Ok(kind)
    }

    fn type_alias(
        &mut self,
        state: &mut ResolutionState,
        alias: &ast::TypeAlias,
    ) -> Result<ItemKind> {
        let kind = match &alias.kind {
            ast::TypeAliasKind::Func(f) => ItemKind::Type(Type::Func(self.func_type(
                state,
                &f.params,
                f.results.as_ref(),
                FuncKind::Free,
            )?)),
            ast::TypeAliasKind::Type(ty) => match ty {
                ast::Type::Ident(id) => {
                    let item = &self.items[self.require(state, id)?];
                    match item.kind {
                        ItemKind::Type(Type::Value(id)) => ItemKind::Type(Type::Value(
                            self.definitions
                                .types
                                .alloc(DefinedType::Alias(ValueType::Defined(id))),
                        )),
                        ItemKind::Type(Type::Func(id)) | ItemKind::Func(id) => {
                            ItemKind::Type(Type::Func(id))
                        }
                        _ => {
                            return Err(new_error_with_span(
                                state.document.path,
                                id.0,
                                format!(
                                    "`{id}` ({kind}) cannot be used in a type alias",
                                    kind = item.kind.display(&self.definitions),
                                    id = id.as_str(),
                                ),
                            ))
                        }
                    }
                }
                _ => {
                    let ty = self.ty(state, ty)?;
                    ItemKind::Type(Type::Value(
                        self.definitions.types.alloc(DefinedType::Alias(ty)),
                    ))
                }
            },
        };

        let id = self.items.alloc(Item {
            kind,
            source: ItemSource::Definition,
        });

        self.register_name(state, alias.id, id)?;
        Ok(kind)
    }

    fn func_type_ref(
        &mut self,
        state: &ResolutionState,
        r: &ast::FuncTypeRef,
        kind: FuncKind,
    ) -> Result<FuncId> {
        match r {
            ast::FuncTypeRef::Func(ty) => {
                self.func_type(state, &ty.params, ty.results.as_ref(), kind)
            }
            ast::FuncTypeRef::Ident(id) => {
                let item = &self.items[self.require(state, id)?];
                match item.kind {
                    ItemKind::Type(Type::Func(id)) | ItemKind::Func(id) => Ok(id),
                    _ => Err(new_error_with_span(
                        state.document.path,
                        id.0,
                        format!(
                            "`{id}` ({kind}) is not a function type",
                            kind = item.kind.display(&self.definitions),
                            id = id.as_str()
                        ),
                    )),
                }
            }
        }
    }

    fn ty(&mut self, state: &ResolutionState, ty: &ast::Type) -> Result<ValueType> {
        match ty {
            ast::Type::U8(_) => Ok(ValueType::Primitive(PrimitiveType::U8)),
            ast::Type::S8(_) => Ok(ValueType::Primitive(PrimitiveType::S8)),
            ast::Type::U16(_) => Ok(ValueType::Primitive(PrimitiveType::U16)),
            ast::Type::S16(_) => Ok(ValueType::Primitive(PrimitiveType::S16)),
            ast::Type::U32(_) => Ok(ValueType::Primitive(PrimitiveType::U32)),
            ast::Type::S32(_) => Ok(ValueType::Primitive(PrimitiveType::S32)),
            ast::Type::U64(_) => Ok(ValueType::Primitive(PrimitiveType::U64)),
            ast::Type::S64(_) => Ok(ValueType::Primitive(PrimitiveType::S64)),
            ast::Type::Float32(_) => Ok(ValueType::Primitive(PrimitiveType::Float32)),
            ast::Type::Float64(_) => Ok(ValueType::Primitive(PrimitiveType::Float64)),
            ast::Type::Char(_) => Ok(ValueType::Primitive(PrimitiveType::Char)),
            ast::Type::Bool(_) => Ok(ValueType::Primitive(PrimitiveType::Bool)),
            ast::Type::String(_) => Ok(ValueType::Primitive(PrimitiveType::String)),
            ast::Type::Tuple(v) => {
                let types = v
                    .types
                    .iter()
                    .map(|ty| self.ty(state, ty))
                    .collect::<Result<_>>()?;

                Ok(ValueType::Defined(
                    self.definitions.types.alloc(DefinedType::Tuple(types)),
                ))
            }
            ast::Type::List(l) => {
                let ty = self.ty(state, &l.ty)?;
                Ok(ValueType::Defined(
                    self.definitions.types.alloc(DefinedType::List(ty)),
                ))
            }
            ast::Type::Option(o) => {
                let ty = self.ty(state, &o.ty)?;
                Ok(ValueType::Defined(
                    self.definitions.types.alloc(DefinedType::Option(ty)),
                ))
            }
            ast::Type::Result(r) => {
                let (ok, err) = match &r.specified {
                    Some(s) => {
                        let ok = match &s.ok {
                            ast::OmitType::Omitted(_) => None,
                            ast::OmitType::Type(t) => Some(self.ty(state, t)?),
                        };

                        let err = s.err.as_ref().map(|t| self.ty(state, t)).transpose()?;
                        (ok, err)
                    }
                    None => (None, None),
                };

                Ok(ValueType::Defined(
                    self.definitions
                        .types
                        .alloc(DefinedType::Result { ok, err }),
                ))
            }
            ast::Type::Borrow(b) => {
                let item = &self.items[self.require(state, &b.id)?];
                if let ItemKind::Type(Type::Value(id)) = item.kind {
                    if let DefinedType::Resource(id) = &self.definitions.types[id] {
                        return Ok(ValueType::Defined(
                            self.definitions.types.alloc(DefinedType::Borrow(*id)),
                        ));
                    }
                }

                Err(new_error_with_span(
                    state.document.path,
                    b.id.0,
                    format!(
                        "`{id}` ({kind}) is not a resource type",
                        kind = item.kind.display(&self.definitions),
                        id = b.id.as_str()
                    ),
                ))
            }
            ast::Type::Ident(id) => {
                let item = &self.items[self.require(state, id)?];
                match item.kind {
                    ItemKind::Type(Type::Value(id)) => Ok(ValueType::Defined(id)),
                    _ => Err(new_error_with_span(
                        state.document.path,
                        id.0,
                        format!(
                            "`{id}` ({kind}) cannot be used as a value type",
                            kind = item.kind.display(&self.definitions),
                            id = id.as_str(),
                        ),
                    )),
                }
            }
        }
    }

    fn func_type(
        &mut self,
        state: &ResolutionState,
        func_params: &ast::ParamList,
        func_results: Option<&ast::ResultList>,
        kind: FuncKind,
    ) -> Result<FuncId> {
        let mut params = IndexMap::new();
        for param in &func_params.list {
            if params
                .insert(param.id.as_str().into(), self.ty(state, &param.ty)?)
                .is_some()
            {
                return Err(new_error_with_span(
                    state.document.path,
                    param.id.0,
                    format!("duplicate {kind} parameter `{id}`", id = param.id.as_str()),
                ));
            }
        }

        let results = func_results
            .as_ref()
            .map(|r| match r {
                ast::ResultList::Named { results: r, .. } => {
                    let mut results = IndexMap::new();
                    for result in &r.list {
                        if results
                            .insert(result.id.as_str().into(), self.ty(state, &result.ty)?)
                            .is_some()
                        {
                            return Err(new_error_with_span(
                                state.document.path,
                                result.id.0,
                                format!("duplicate {kind} result `{id}`", id = result.id.as_str()),
                            ));
                        }
                    }
                    Ok(FuncResult::List(results))
                }
                ast::ResultList::Single { ty, .. } => Ok(FuncResult::Scalar(self.ty(state, ty)?)),
            })
            .transpose()?;

        Ok(self.definitions.funcs.alloc(Func { params, results }))
    }

    fn resolve_package<'b>(
        &mut self,
        state: &'b mut ResolutionState,
        name: &ast::PackageName,
    ) -> Result<&'b Package> {
        match state.packages.entry(name.as_str().to_owned()) {
            hash_map::Entry::Occupied(e) => Ok(e.into_mut()),
            hash_map::Entry::Vacant(e) => {
                log::debug!("resolving package `{name}`");
                match state
                    .resolver
                    .as_deref()
                    .and_then(|r| r.resolve(name).transpose())
                    .transpose()
                    .map_err(|e| {
                        let msg =
                            format!("failed to resolve package `{name}`", name = name.as_str());
                        e.context(new_error_with_span(state.document.path, name.span(), msg))
                    })? {
                    Some(bytes) => Ok(e.insert(
                        Package::parse(&mut self.definitions, bytes).map_err(|e| {
                            let msg =
                                format!("failed to parse package `{name}`", name = name.as_str());
                            e.context(new_error_with_span(state.document.path, name.span(), msg))
                        })?,
                    )),
                    None => {
                        return Err(new_error_with_span(
                            state.document.path,
                            name.span(),
                            format!("unknown package `{name}`", name = name.as_str()),
                        ));
                    }
                }
            }
        }
    }

    fn resolve_package_export(
        &mut self,
        state: &mut ResolutionState,
        path: &ast::PackagePath,
    ) -> Result<ItemKind> {
        // Check for reference to local item
        if path.name.as_str() == self.package {
            return self.resolve_local_export(state, path);
        }

        let pkg = self.resolve_package(state, &path.name)?;

        let mut current = 0;
        let mut parent_ty = None;
        let mut found = None;
        for (i, segment) in path.segments.iter().map(|(_, s)| s.as_str()).enumerate() {
            current = i;

            // Look up the first segment in the package definitions
            if i == 0 {
                found = pkg.definitions.get(segment).copied();
                continue;
            }

            // Otherwise, project into the parent based on the current segment
            let (ty, export) = match found.unwrap() {
                // The parent is an interface or instance
                ItemKind::Type(Type::Interface(id)) | ItemKind::Instance(id) => (
                    "interface",
                    self.definitions.interfaces[id]
                        .exports
                        .get(segment)
                        .map(Extern::kind),
                ),
                // The parent is a world or component or component instantiation
                ItemKind::Type(Type::World(id))
                | ItemKind::Component(id)
                | ItemKind::Instantiation(id) => (
                    "world",
                    self.definitions.worlds[id]
                        .exports
                        .get(segment)
                        .map(Extern::kind),
                ),
                ItemKind::Func(_) => ("func", None),
                ItemKind::Type(_) => ("type", None),
                ItemKind::Module(_) => ("module", None),
                ItemKind::Value(_) => ("value", None),
            };

            parent_ty = Some(ty);
            found = export;
            if found.is_none() {
                break;
            }
        }

        found.ok_or_else(|| {
            let segment = path.segments[current].1;
            new_error_with_span(
                state.document.path,
                segment.0,
                format!(
                    "{prev}package `{name}` has no export named `{segment}`",
                    prev = match parent_ty {
                        Some(parent) => {
                            format!(
                                "{parent} `{path}` in ",
                                path = path.segments[..current].iter().fold(
                                    String::new(),
                                    |mut path, (_, s)| {
                                        if !path.is_empty() {
                                            path.push('/');
                                        }
                                        path.push_str(s.as_str());
                                        path
                                    }
                                )
                            )
                        }
                        None => String::new(),
                    },
                    name = path.name.as_str(),
                    segment = segment.as_str(),
                ),
            )
        })
    }

    fn resolve_local_export(
        &self,
        state: &ResolutionState,
        path: &ast::PackagePath,
    ) -> Result<ItemKind> {
        log::debug!("resolving local path `{path}`");

        let mut segments = path.segments.iter().map(|(_, s)| s);
        let id = segments.next().unwrap();
        let item =
            &self.items[self.scopes[state.root_scope]
                .get(id.as_str())
                .ok_or_else(|| {
                    new_error_with_span(
                        state.document.path,
                        id.0,
                        format!("undefined name `{id}`", id = id.as_str()),
                    )
                })?];

        let mut current = id;
        let mut kind = item.kind;
        for segment in segments {
            let exports = match kind {
                ItemKind::Type(Type::Interface(id)) | ItemKind::Instance(id) => {
                    &self.definitions.interfaces[id].exports
                }
                ItemKind::Type(Type::World(id)) | ItemKind::Component(id) => {
                    &self.definitions.worlds[id].exports
                }
                _ => {
                    return Err(new_error_with_span(
                        state.document.path,
                        current.0,
                        format!(
                            "`{id}` ({kind}) has no exports",
                            kind = item.kind.display(&self.definitions),
                            id = current.as_str()
                        ),
                    ))
                }
            };

            kind = exports
                .get(segment.as_str())
                .map(Extern::kind)
                .ok_or_else(|| {
                    new_error_with_span(
                        state.document.path,
                        current.0,
                        format!(
                            "`{id}` ({kind}) has no export named `{segment}`",
                            kind = item.kind.display(&self.definitions),
                            id = current.as_str(),
                            segment = segment.as_str(),
                        ),
                    )
                })?;
            current = segment;
        }

        Ok(kind)
    }

    fn expr<'a>(&mut self, state: &mut ResolutionState<'a>, expr: &'a ast::Expr) -> Result<ItemId> {
        let mut item = self.primary_expr(state, &expr.primary)?;

        for expr in &expr.postfix {
            item = self.postfix_expr(state, item, expr)?;
        }

        Ok(item)
    }

    fn primary_expr<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        expr: &'a ast::PrimaryExpr<'a>,
    ) -> Result<ItemId> {
        match expr {
            ast::PrimaryExpr::New(n) => self.new_expr(state, n),
            ast::PrimaryExpr::Nested(n) => self.expr(state, &n.expr),
            ast::PrimaryExpr::Ident(i) => Ok(self.require(state, i)?),
        }
    }

    fn new_expr<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        expr: &'a ast::NewExpr<'a>,
    ) -> Result<ItemId> {
        let pkg = self.resolve_package(state, &expr.package_name)?;
        let ty = pkg.ty;
        let require_all = expr.body.ellipsis.is_none();

        let mut arguments: IndexMap<String, ItemId> = Default::default();
        for arg in &expr.body.arguments {
            let (name, item, span) = match arg {
                ast::InstantiationArgument::Named(arg) => {
                    self.named_instantiation_arg(state, arg, ty)?
                }
                ast::InstantiationArgument::Ident(id) => {
                    self.ident_instantiation_arg(state, id, ty)?
                }
            };

            let world = &self.definitions.worlds[ty];
            let expected = world.imports.get(&name).ok_or_else(|| {
                new_error_with_span(
                    state.document.path,
                    span,
                    format!(
                        "component `{pkg}` has no import named `{name}`",
                        pkg = expr.package_name.as_str(),
                    ),
                )
            })?;

            SubtypeChecker::new(&self.definitions)
                .is_subtype(expected.kind(), self.items[item].kind)
                .map_err(|e| {
                    e.context(new_error_with_span(
                        state.document.path,
                        span,
                        format!("mismatched instantiation argument `{name}`"),
                    ))
                })?;

            let prev = arguments.insert(name.clone(), item);
            if prev.is_some() {
                return Err(new_error_with_span(
                    state.document.path,
                    span,
                    format!("duplicate instantiation argument `{name}`"),
                ));
            }
        }

        if require_all {
            let world = &self.definitions.worlds[ty];
            if let Some((missing, _)) = world
                .imports
                .iter()
                .find(|(n, _)| !arguments.contains_key(*n))
            {
                return Err(new_error_with_span(
                    state.document.path,
                    expr.package_name.span(),
                    format!(
                        "missing instantiation argument `{missing}` for package `{pkg}`",
                        pkg = expr.package_name.as_str(),
                    ),
                ));
            }
        }

        Ok(self.items.alloc(Item {
            kind: ItemKind::Instantiation(ty),
            source: ItemSource::Instantiation { arguments },
        }))
    }

    fn named_instantiation_arg<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        arg: &'a ast::NamedInstantiationArgument<'a>,
        world: WorldId,
    ) -> Result<(String, ItemId, Span<'a>)> {
        let item = self.expr(state, &arg.expr)?;

        let name = match &arg.name {
            ast::InstantiationArgumentName::Ident(ident) => Self::find_matching_interface_name(
                ident.as_str(),
                &self.definitions.worlds[world].imports,
            )
            .unwrap_or_else(|| ident.as_str()),
            ast::InstantiationArgumentName::String(name) => name.as_str(),
        };

        Ok((name.to_owned(), item, arg.name.span()))
    }

    fn ident_instantiation_arg<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        ident: &ast::Ident<'a>,
        world: WorldId,
    ) -> Result<(String, ItemId, Span<'a>)> {
        let item_id = self.require(state, ident)?;
        let item = &self.items[item_id];
        let world = &self.definitions.worlds[world];

        // If the item is an instance with an id, try the id.
        if let ItemKind::Instance(id) = item.kind {
            if let Some(id) = &self.definitions.interfaces[id].id {
                if world.imports.contains_key(id.as_str()) {
                    return Ok((id.clone(), item_id, ident.0));
                }
            }
        }

        // If the item comes from an import or an alias, try the name associated with it
        match &item.source {
            ItemSource::Import { with: Some(name) } | ItemSource::Alias { export: name, .. } => {
                if world.imports.contains_key(name) {
                    return Ok((name.clone(), item_id, ident.0));
                }
            }
            _ => {}
        }

        // Fall back to searching for a matching interface name, provided it is not ambiguous
        // For example, match `foo:bar/baz` if `baz` is the identifier and the only match
        if let Some(name) = Self::find_matching_interface_name(ident.as_str(), &world.imports) {
            return Ok((name.to_owned(), item_id, ident.0));
        }

        // Finally default to the id itself
        Ok((ident.as_str().to_owned(), item_id, ident.0))
    }

    fn find_matching_interface_name<'a>(name: &str, externs: &'a ExternMap) -> Option<&'a str> {
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

    fn postfix_expr<'a>(
        &mut self,
        state: &mut ResolutionState<'a>,
        item: ItemId,
        expr: &'a ast::PostfixExpr<'a>,
    ) -> Result<ItemId> {
        match expr {
            ast::PostfixExpr::Access(expr) => {
                let exports = self.instance_exports(item, state, expr.id.0)?;
                let name: Cow<'a, str> =
                    Self::find_matching_interface_name(expr.id.as_str(), exports)
                        .map(|s| s.to_string().into())
                        .unwrap_or_else(|| expr.id.as_str().into());
                self.access_expr(state, item, name.as_ref(), expr.id.0)
            }
            ast::PostfixExpr::NamedAccess(expr) => {
                self.access_expr(state, item, expr.string.as_str(), expr.string.0)
            }
        }
    }

    fn instance_exports(
        &self,
        item: ItemId,
        state: &ResolutionState,
        span: Span,
    ) -> Result<&ExternMap> {
        match self.items[item].kind {
            ItemKind::Instance(id) => Ok(&self.definitions.interfaces[id].exports),
            ItemKind::Instantiation(id) => Ok(&self.definitions.worlds[id].exports),
            ItemKind::Type(Type::Interface(_)) => Err(new_error_with_span(
                state.document.path,
                span,
                "an interface cannot be accessed",
            )),
            ItemKind::Type(ty) => Err(new_error_with_span(
                state.document.path,
                span,
                format!(
                    "a {ty} cannot be accessed",
                    ty = ty.display(&self.definitions)
                ),
            )),
            ItemKind::Func(_) => Err(new_error_with_span(
                state.document.path,
                span,
                "a function cannot be accessed",
            )),
            ItemKind::Component(_) => Err(new_error_with_span(
                state.document.path,
                span,
                "a component cannot be accessed",
            )),
            ItemKind::Module(_) => Err(new_error_with_span(
                state.document.path,
                span,
                "a module cannot be accessed",
            )),
            ItemKind::Value(_) => Err(new_error_with_span(
                state.document.path,
                span,
                "a value cannot be accessed",
            )),
        }
    }

    fn access_expr(
        &mut self,
        state: &mut ResolutionState,
        item: ItemId,
        name: &str,
        span: Span,
    ) -> Result<ItemId> {
        let exports = self.instance_exports(item, state, span)?;
        let kind = exports.get(name).map(Extern::kind).ok_or_else(|| {
            new_error_with_span(
                state.document.path,
                span,
                format!("the instance has no export named `{name}`"),
            )
        })?;

        match state.aliases.entry((item, name.to_owned())) {
            hash_map::Entry::Occupied(e) => Ok(*e.get()),
            hash_map::Entry::Vacant(e) => {
                let id = self.items.alloc(Item {
                    kind,
                    source: ItemSource::Alias {
                        item,
                        export: name.to_owned(),
                    },
                });
                Ok(*e.insert(id))
            }
        }
    }
}
