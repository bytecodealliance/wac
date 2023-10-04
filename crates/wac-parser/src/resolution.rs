//! Module for resolving WAC documents.

use self::package::Package;
use crate::ast::{self, new_error_with_span};
use anyhow::{Context, Result};
use id_arena::{Arena, Id};
use indexmap::{IndexMap, IndexSet};
use pest::{Position, Span};
use serde::{Serialize, Serializer};
use std::{
    collections::{hash_map, HashMap, HashSet},
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
}

impl FileSystemPackageResolver {
    /// Creates a new `FileSystemPackageResolver` with the given root directory.
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }
}

impl Default for FileSystemPackageResolver {
    fn default() -> Self {
        Self::new("deps")
    }
}

impl PackageResolver for FileSystemPackageResolver {
    fn resolve(&self, name: &ast::PackageName) -> Result<Option<Vec<u8>>> {
        let mut path = self.root.clone();
        for part in &name.parts {
            path.push(part.as_str());
        }

        // First check to see if a directory `<root>/ns*/name` exists.
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

        // Otherwise, check if `<root>/ns*/name.wasm` exists as a file
        path.set_extension("wasm");
        if !path.is_file() {
            log::debug!("package `{path}` does not exist", path = path.display());
            return Ok(None);
        }

        log::debug!("loading package from `{path}`", path = path.display());
        fs::read(&path)
            .with_context(|| format!("failed to read package `{path}`", path = path.display()))
            .map(Some)
    }
}

/// An identifier for scopes.
pub type ScopeId = Id<Scope>;

/// Represents a defined name.
#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Name {
    /// The starting position of the name.
    pub start: usize,
    /// The ending position of the name.
    pub end: usize,
    /// The extern kind of name.
    pub kind: ExternKind,
}

/// Represents a scope for names.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]

pub struct Scope {
    #[serde(serialize_with = "serialize_optional_id")]
    parent: Option<ScopeId>,
    names: IndexMap<String, Name>,
}

impl Scope {
    /// Gets a name from the scope.
    pub fn get(&self, name: &str) -> Option<Name> {
        self.names.get(name).copied()
    }

    /// Iterates all names in the scope.
    pub fn iter(&self) -> impl Iterator<Item = &Name> {
        self.names.values()
    }
}

struct ResolutionState<'a> {
    document: &'a ast::Document<'a>,
    resolver: Option<Box<dyn PackageResolver>>,
    current_scope: ScopeId,
    packages: HashMap<String, Package>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FuncKind {
    Free,
    Method,
    Static,
    Constructor,
}

impl fmt::Display for FuncKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FuncKind::Free => write!(f, "function"),
            FuncKind::Method | FuncKind::Static => write!(f, "method"),
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
    /// The name scopes in the resolution.
    #[serde(serialize_with = "serialize_arena")]
    pub scopes: Arena<Scope>,
    /// The id of the root scope.
    #[serde(serialize_with = "serialize_id")]
    pub root_scope: ScopeId,
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
            names: Default::default(),
        });

        let mut resolution = ResolvedDocument {
            package: package.into(),
            definitions: Default::default(),
            scopes,
            root_scope,
        };

        let mut state = ResolutionState {
            document,
            resolver,
            current_scope: root_scope,
            packages: Default::default(),
        };

        for stmt in &document.statements {
            match &stmt.stmt {
                ast::Statement::Import(i) => resolution.import(&mut state, i)?,
                ast::Statement::Type(t) => resolution.type_statement(&mut state, t)?,
                ast::Statement::Let(_) => todo!("implement let statements"),
                ast::Statement::Export(_) => todo!("implement export statements"),
            }
        }

        Ok(resolution)
    }

    /// Encode the resolved document as a WebAssembly component.
    pub fn encode(&self) -> Result<Vec<u8>> {
        todo!("implement encoding")
    }

    fn get(&self, state: &ResolutionState, id: &ast::Ident) -> Option<Name> {
        let mut current = &self.scopes[state.current_scope];
        loop {
            if let Some(name) = current.get(id.as_str()) {
                return Some(name);
            }

            current = &self.scopes[current.parent?];
        }
    }

    fn require(&self, state: &ResolutionState, id: &ast::Ident) -> Result<Name> {
        self.get(state, id).ok_or_else(|| {
            new_error_with_span(
                format!("undefined name `{id}`", id = id.as_str()),
                state.document.path,
                id.0,
            )
        })
    }

    fn push_scope(&mut self, state: &mut ResolutionState) {
        state.current_scope = self.scopes.alloc(Scope {
            parent: Some(state.current_scope),
            names: Default::default(),
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
        state: &ResolutionState,
        id: ast::Ident,
        kind: ExternKind,
    ) -> Result<()> {
        if let Some(prev) = self.scopes[state.current_scope].names.insert(
            id.as_str().to_owned(),
            Name {
                start: id.0.start(),
                end: id.0.end(),
                kind,
            },
        ) {
            let (line, column) = Position::new(id.0.get_input(), prev.start)
                .unwrap()
                .line_col();
            return Err(new_error_with_span(
                format!(
                    "`{id}` was previously defined at {path}:{line}:{column}",
                    id = id.as_str(),
                    path = state.document.path.display(),
                ),
                state.document.path,
                id.0,
            ));
        }

        Ok(())
    }

    fn import(&mut self, state: &mut ResolutionState, stmt: &ast::ImportStatement) -> Result<()> {
        let kind = match &stmt.ty {
            ast::ImportType::Package(p) => self.resolve_package_export(state, p)?,
            ast::ImportType::Func(ty) => ExternKind::Func(self.func_type(
                state,
                &ty.params,
                ty.results.as_ref(),
                FuncKind::Free,
            )?),
            ast::ImportType::Interface(i) => self.inline_interface(state, i)?,
            ast::ImportType::Ident(id) => self.require(state, id)?.kind,
        };

        // Promote function types, instance types, and component types to functions, instances, and components
        let kind = match kind {
            ExternKind::Type(ExternType::Func(id)) => ExternKind::Func(id),
            ExternKind::Type(ExternType::Interface(id)) => ExternKind::Instance(id),
            ExternKind::Type(ExternType::World(id)) => ExternKind::Component(id),
            _ => kind,
        };

        self.register_name(state, stmt.id, kind)
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

    fn inline_interface(
        &mut self,
        state: &mut ResolutionState,
        iface: &ast::InlineInterface,
    ) -> Result<ExternKind> {
        self.push_scope(state);

        let mut ty = Interface {
            id: None,
            exports: Default::default(),
            scope: Some(state.current_scope),
        };

        self.interface_body(state, None, &iface.body, &mut ty)?;

        self.pop_scope(state);

        Ok(ExternKind::Type(ExternType::Interface(
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

        let id = self.definitions.interfaces.alloc(ty);
        self.register_name(state, decl.id, ExternKind::Type(ExternType::Interface(id)))
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

        let id = self.definitions.worlds.alloc(ty);
        self.register_name(state, decl.id, ExternKind::Type(ExternType::World(id)))
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
                    let kind: ExternKind = self.type_decl(state, decl)?;
                    let prev = ty
                        .exports
                        .insert(decl.id().as_str().into(), Extern::Kind(kind));
                    assert!(prev.is_none(), "duplicate type in scope");
                }
                ast::InterfaceItemStatement::Export(e) => {
                    let kind =
                        ExternKind::Func(self.func_type_ref(state, &e.ty, FuncKind::Free)?);
                    if ty
                        .exports
                        .insert(e.id.as_str().into(), Extern::Kind(kind))
                        .is_some()
                    {
                        return Err(new_error_with_span(
                            match name {
                                Some(name) => format!(
                                    "duplicate interface export `{id}` for interface `{name}`",
                                    id = e.id.as_str()
                                ),
                                None => {
                                    format!("duplicate interface export `{id}`", id = e.id.as_str())
                                }
                            },
                            state.document.path,
                            e.id.0,
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
                    format!(
                        "{dir} `{name}` conflicts with existing {dir} of the same name in world `{world}`",
                        dir = if import { "import" } else { "export" },
                    ),
                    state.document.path,
                    span,
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
                            let name = self.require(state, id)?;
                            match name.kind {
                                ExternKind::Type(ExternType::Interface(id))
                                | ExternKind::Instance(id) => ExternKind::Instance(id),
                                ExternKind::Type(ExternType::Func(id)) | ExternKind::Func(id) => {
                                    ExternKind::Func(id)
                                }
                                _ => {
                                    return Err(new_error_with_span(
                                        format!(
                                            "{kind} `{id}` is not a function type or interface",
                                            kind = name.kind,
                                            id = id.as_str(),
                                        ),
                                        state.document.path,
                                        id.0,
                                    ))
                                }
                            }
                        }
                        ast::ExternType::Func(f) => ExternKind::Func(self.func_type(
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
                    let name = self.require(state, id)?;
                    match name.kind {
                        ExternKind::Type(ExternType::Interface(iface_ty_id))
                        | ExternKind::Instance(iface_ty_id) => {
                            let iface_id = self.definitions.interfaces[iface_ty_id]
                                .id
                                .as_ref()
                                .expect("expected an interface id");
                            check_name(iface_id, id.0, ty)?;
                            (iface_id.clone(), ExternKind::Instance(iface_ty_id))
                        }
                        _ => {
                            return Err(new_error_with_span(
                                format!(
                                    "{kind} `{id}` is not an interface",
                                    kind = name.kind,
                                    id = id.as_str()
                                ),
                                state.document.path,
                                id.0,
                            ))
                        }
                    }
                }
                ast::InterfaceRef::Path(p) => match self.resolve_package_export(state, p)? {
                    ExternKind::Type(ExternType::Interface(id)) | ExternKind::Instance(id) => {
                        let name = self.definitions.interfaces[id]
                            .id
                            .as_ref()
                            .expect("expected an interface id");
                        check_name(name, p.span(), ty)?;
                        (name.clone(), ExternKind::Instance(id))
                    }
                    ty => {
                        return Err(new_error_with_span(
                            format!("{ty} `{path}` is not an interface", path = p.as_str()),
                            state.document.path,
                            p.span(),
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
                    format!(
                        "duplicate `{name}` in world include `with` clause",
                        name = item.name,
                    ),
                    state.document.path,
                    item.name.0,
                ));
            }
        }

        let id = match &stmt.world {
            ast::WorldRef::Ident(id) => {
                let name = self.require(state, id)?;
                match name.kind {
                    ExternKind::Type(ExternType::World(id)) | ExternKind::Component(id) => id,
                    kind => {
                        return Err(new_error_with_span(
                            format!("{kind} `{id}` is not a world", id = id.as_str()),
                            state.document.path,
                            id.0,
                        ))
                    }
                }
            }
            ast::WorldRef::Path(path) => match self.resolve_package_export(state, path)? {
                ExternKind::Type(ExternType::World(id)) | ExternKind::Component(id) => id,
                ty => {
                    return Err(new_error_with_span(
                        format!("{ty} `{path}` is not a world", path = path.as_str()),
                        state.document.path,
                        path.span(),
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
                format!(
                    "world `{other}` does not have an import or export with kebab-name `{name}`",
                    other = stmt.world.name(),
                    name = missing.name.as_str(),
                ),
                state.document.path,
                missing.name.0,
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
                    format!(
                        "{dir} `{name}` from world `{other}` conflicts with {dir} of the same name in world `{world}`{hint}",
                        dir = if import { "import" } else { "export" },
                        other = stmt.world.name(),
                        hint = if stmt.with.is_some() { "" } else {
                            " (consider using a `with` clause to use a different name)"
                        }
                    ),
                    path,
                    span,
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
                ExternKind::Type(ExternType::Interface(id)) | ExternKind::Instance(id) => {
                    (id, path.as_str())
                }
                ty => {
                    return Err(new_error_with_span(
                        format!("{ty} `{path}` is not an interface", path = path.as_str()),
                        state.document.path,
                        path.span(),
                    ))
                }
            },
            ast::UsePath::Ident(id) => {
                let name = self.require(state, id)?;
                match name.kind {
                    ExternKind::Type(ExternType::Interface(iface_ty_id))
                    | ExternKind::Instance(iface_ty_id) => (iface_ty_id, id.as_str()),
                    kind => {
                        return Err(new_error_with_span(
                            format!("{kind} `{id}` is not an interface", id = id.as_str()),
                            state.document.path,
                            id.0,
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
                        format!(
                            "type `{item}` is not defined in interface `{name}`",
                            item = item.id.as_str()
                        ),
                        state.document.path,
                        item.id.0,
                    )
                })?;

            let kind = ext.kind();
            match kind {
                ExternKind::Type(ExternType::Value(ty)) => {
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
                                    Extern::Kind(ExternKind::Instance(interface)),
                                );
                            }

                            cur = iface.exports[export_index];
                        }
                    }

                    externs.insert(ident.as_str().into(), new_extern);
                    self.register_name(state, ident, kind)?;
                }
                _ => {
                    return Err(new_error_with_span(
                        format!(
                            "{kind} `{item}` is not a value type in interface `{name}`",
                            item = item.id.as_str()
                        ),
                        state.document.path,
                        item.id.0,
                    ));
                }
            }
        }

        Ok(())
    }

    fn type_decl(
        &mut self,
        state: &mut ResolutionState,
        decl: &ast::TypeDecl,
    ) -> Result<ExternKind> {
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
    ) -> Result<ExternKind> {
        // Resources are allowed to be self-referential, so we need to allocate the resource
        // before we resolve the methods.
        let id = self.definitions.resources.alloc(Resource {
            methods: Default::default(),
        });
        let kind = ExternKind::Type(ExternType::Value(
            self.definitions.types.alloc(DefinedType::Resource(id)),
        ));

        self.register_name(state, decl.id, kind)?;

        self.definitions.resources[id].methods = match &decl.body {
            ast::ResourceBody::Empty(_) => Vec::new(),
            ast::ResourceBody::Methods { methods, .. } => {
                let mut constructor = false;
                let mut names = HashSet::new();

                methods
                    .iter()
                    .map(|(m, _)| match m {
                        ast::ResourceMethod::Constructor(ast::Constructor { keyword, params }) => {
                            if constructor {
                                return Err(new_error_with_span(
                                    format!(
                                        "duplicate constructor for resource `{res}`",
                                        res = decl.id
                                    ),
                                    state.document.path,
                                    keyword.0,
                                ));
                            }

                            constructor = true;
                            Ok(ResourceMethod::Constructor(self.func_type(
                                state,
                                params,
                                None,
                                FuncKind::Constructor,
                            )?))
                        }
                        ast::ResourceMethod::Method(ast::Method {
                            id, func, keyword, ..
                        }) => {
                            if !names.insert(id.as_str()) {
                                return Err(new_error_with_span(
                                    format!(
                                        "duplicate method `{id}` for resource `{res}`",
                                        id = id.as_str(),
                                        res = decl.id.as_str()
                                    ),
                                    state.document.path,
                                    id.0,
                                ));
                            }

                            if keyword.is_some() {
                                Ok(ResourceMethod::Static {
                                    name: id.as_str().into(),
                                    ty: self.func_type_ref(state, func, FuncKind::Method)?,
                                })
                            } else {
                                Ok(ResourceMethod::Instance {
                                    name: id.as_str().into(),
                                    ty: self.func_type_ref(state, func, FuncKind::Method)?,
                                })
                            }
                        }
                    })
                    .collect::<Result<_>>()?
            }
        };

        Ok(kind)
    }

    fn variant_decl(
        &mut self,
        state: &mut ResolutionState,
        decl: &ast::VariantDecl,
    ) -> Result<ExternKind> {
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
                    format!(
                        "duplicate case `{case}` for variant type `{ty}`",
                        case = case.id,
                        ty = decl.id
                    ),
                    state.document.path,
                    case.id.0,
                ));
            }
        }

        let kind = ExternKind::Type(ExternType::Value(
            self.definitions
                .types
                .alloc(DefinedType::Variant(Variant { cases })),
        ));
        self.register_name(state, decl.id, kind)?;
        Ok(kind)
    }

    fn record_decl(
        &mut self,
        state: &mut ResolutionState,
        decl: &ast::RecordDecl,
    ) -> Result<ExternKind> {
        let mut fields = IndexMap::new();
        for field in &decl.body.fields {
            if fields
                .insert(field.id.as_str().into(), self.ty(state, &field.ty)?)
                .is_some()
            {
                return Err(new_error_with_span(
                    format!(
                        "duplicate field `{field}` for record type `{ty}`",
                        field = field.id,
                        ty = decl.id
                    ),
                    state.document.path,
                    field.id.0,
                ));
            }
        }

        let kind = ExternKind::Type(ExternType::Value(
            self.definitions
                .types
                .alloc(DefinedType::Record(Record { fields })),
        ));
        self.register_name(state, decl.id, kind)?;
        Ok(kind)
    }

    fn flags_decl(
        &mut self,
        state: &mut ResolutionState,
        decl: &ast::FlagsDecl,
    ) -> Result<ExternKind> {
        let mut flags = IndexSet::new();
        for flag in &decl.body.flags {
            if !flags.insert(flag.as_str().into()) {
                return Err(new_error_with_span(
                    format!(
                        "duplicate flag `{flag}` for flags type `{ty}`",
                        ty = decl.id
                    ),
                    state.document.path,
                    flag.0,
                ));
            }
        }

        let kind = ExternKind::Type(ExternType::Value(
            self.definitions
                .types
                .alloc(DefinedType::Flags(Flags(flags))),
        ));
        self.register_name(state, decl.id, kind)?;
        Ok(kind)
    }

    fn enum_decl(
        &mut self,
        state: &mut ResolutionState,
        decl: &ast::EnumDecl,
    ) -> Result<ExternKind> {
        let mut cases = IndexSet::new();
        for case in &decl.body.cases {
            if !cases.insert(case.as_str().into()) {
                return Err(new_error_with_span(
                    format!("duplicate case `{case}` for enum type `{ty}`", ty = decl.id),
                    state.document.path,
                    case.0,
                ));
            }
        }

        let kind = ExternKind::Type(ExternType::Value(
            self.definitions.types.alloc(DefinedType::Enum(Enum(cases))),
        ));
        self.register_name(state, decl.id, kind)?;
        Ok(kind)
    }

    fn type_alias(
        &mut self,
        state: &mut ResolutionState,
        alias: &ast::TypeAlias,
    ) -> Result<ExternKind> {
        let kind = match &alias.kind {
            ast::TypeAliasKind::Func(f) => ExternKind::Type(ExternType::Func(self.func_type(
                state,
                &f.params,
                f.results.as_ref(),
                FuncKind::Free,
            )?)),
            ast::TypeAliasKind::Type(ty) => match ty {
                ast::Type::Ident(id) => {
                    let name = self.require(state, id)?;
                    match name.kind {
                        ExternKind::Type(ExternType::Value(id)) => {
                            ExternKind::Type(ExternType::Value(
                                self.definitions
                                    .types
                                    .alloc(DefinedType::Alias(Type::Defined(id))),
                            ))
                        }
                        ExternKind::Type(ExternType::Func(id)) | ExternKind::Func(id) => {
                            ExternKind::Type(ExternType::Func(id))
                        }
                        _ => {
                            return Err(new_error_with_span(
                                format!(
                                    "{kind} `{id}` cannot be used in a type alias",
                                    kind = name.kind,
                                    id = id.as_str(),
                                ),
                                state.document.path,
                                id.0,
                            ))
                        }
                    }
                }
                _ => {
                    let ty = self.ty(state, ty)?;
                    ExternKind::Type(ExternType::Value(
                        self.definitions.types.alloc(DefinedType::Alias(ty)),
                    ))
                }
            },
        };

        self.register_name(state, alias.id, kind)?;
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
                let name = self.require(state, id)?;
                match name.kind {
                    ExternKind::Type(ExternType::Func(id)) | ExternKind::Func(id) => Ok(id),
                    _ => Err(new_error_with_span(
                        format!(
                            "{kind} `{id}` is not a function type",
                            kind = name.kind,
                            id = id.as_str()
                        ),
                        state.document.path,
                        id.0,
                    )),
                }
            }
        }
    }

    fn ty(&mut self, state: &ResolutionState, ty: &ast::Type) -> Result<Type> {
        match ty {
            ast::Type::U8(_) => Ok(Type::Primitive(PrimitiveType::U8)),
            ast::Type::S8(_) => Ok(Type::Primitive(PrimitiveType::S8)),
            ast::Type::U16(_) => Ok(Type::Primitive(PrimitiveType::U16)),
            ast::Type::S16(_) => Ok(Type::Primitive(PrimitiveType::S16)),
            ast::Type::U32(_) => Ok(Type::Primitive(PrimitiveType::U32)),
            ast::Type::S32(_) => Ok(Type::Primitive(PrimitiveType::S32)),
            ast::Type::U64(_) => Ok(Type::Primitive(PrimitiveType::U64)),
            ast::Type::S64(_) => Ok(Type::Primitive(PrimitiveType::S64)),
            ast::Type::Float32(_) => Ok(Type::Primitive(PrimitiveType::Float32)),
            ast::Type::Float64(_) => Ok(Type::Primitive(PrimitiveType::Float64)),
            ast::Type::Char(_) => Ok(Type::Primitive(PrimitiveType::Char)),
            ast::Type::Bool(_) => Ok(Type::Primitive(PrimitiveType::Bool)),
            ast::Type::String(_) => Ok(Type::Primitive(PrimitiveType::String)),
            ast::Type::Tuple(v) => {
                let types = v
                    .types
                    .iter()
                    .map(|ty| self.ty(state, ty))
                    .collect::<Result<_>>()?;

                Ok(Type::Defined(
                    self.definitions.types.alloc(DefinedType::Tuple(types)),
                ))
            }
            ast::Type::List(l) => {
                let ty = self.ty(state, &l.ty)?;
                Ok(Type::Defined(
                    self.definitions.types.alloc(DefinedType::List(ty)),
                ))
            }
            ast::Type::Option(o) => {
                let ty = self.ty(state, &o.ty)?;
                Ok(Type::Defined(
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

                Ok(Type::Defined(
                    self.definitions
                        .types
                        .alloc(DefinedType::Result { ok, err }),
                ))
            }
            ast::Type::Borrow(b) => {
                let name = self.require(state, &b.id)?;
                if let ExternKind::Type(ExternType::Value(id)) = name.kind {
                    if let DefinedType::Resource(id) = &self.definitions.types[id] {
                        return Ok(Type::Defined(
                            self.definitions.types.alloc(DefinedType::Borrow(*id)),
                        ));
                    }
                }

                Err(new_error_with_span(
                    format!(
                        "{kind} `{id}` is not a resource type",
                        kind = name.kind,
                        id = b.id.as_str()
                    ),
                    state.document.path,
                    b.id.0,
                ))
            }
            ast::Type::Ident(id) => {
                let name = self.require(state, id)?;
                match name.kind {
                    ExternKind::Type(ExternType::Value(id)) => Ok(Type::Defined(id)),
                    _ => Err(new_error_with_span(
                        format!(
                            "{kind} `{id}` cannot be used as a value type",
                            kind = name.kind,
                            id = id.as_str(),
                        ),
                        state.document.path,
                        id.0,
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
                    format!("duplicate {kind} parameter `{id}`", id = param.id.as_str()),
                    state.document.path,
                    param.id.0,
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
                                format!("duplicate {kind} result `{id}`", id = result.id.as_str()),
                                state.document.path,
                                result.id.0,
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

    fn resolve_package_export(
        &mut self,
        state: &mut ResolutionState,
        path: &ast::PackagePath,
    ) -> Result<ExternKind> {
        // Check for reference to local item
        if path.name.as_str() == self.package {
            return self.resolve_local_export(state, path);
        }

        log::debug!("resolving package path `{path}`");
        let pkg = match state.packages.entry(path.name.as_str().to_owned()) {
            hash_map::Entry::Occupied(e) => e.into_mut(),
            hash_map::Entry::Vacant(e) => match state
                .resolver
                .as_deref()
                .and_then(|r| r.resolve(&path.name).transpose())
                .transpose()
                .map_err(|e| {
                    new_error_with_span(format!("{e:#}"), state.document.path, path.name.span())
                })? {
                Some(bytes) => {
                    e.insert(Package::parse(&mut self.definitions, bytes).map_err(|e| {
                        new_error_with_span(
                            format!("failed to parse package `{name}`: {e}", name = path.name),
                            state.document.path,
                            path.name.span(),
                        )
                    })?)
                }
                None => {
                    return Err(new_error_with_span(
                        format!("unknown package `{name}`", name = path.name.as_str()),
                        state.document.path,
                        path.name.span(),
                    ));
                }
            },
        };

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
                ExternKind::Type(ExternType::Interface(id)) | ExternKind::Instance(id) => (
                    "interface",
                    self.definitions.interfaces[id]
                        .exports
                        .get(segment)
                        .map(Extern::kind),
                ),
                // The parent is a world or component
                ExternKind::Type(ExternType::World(id)) | ExternKind::Component(id) => (
                    "world",
                    self.definitions.worlds[id]
                        .exports
                        .get(segment)
                        .map(Extern::kind),
                ),
                ExternKind::Func(_) => ("func", None),
                ExternKind::Type(_) => ("type", None),
                ExternKind::Module(_) => ("module", None),
                ExternKind::Value(_) => ("value", None),
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
                state.document.path,
                segment.0,
            )
        })
    }

    fn resolve_local_export(
        &self,
        state: &ResolutionState,
        path: &ast::PackagePath,
    ) -> Result<ExternKind> {
        log::debug!("resolving local path `{path}`");

        let mut segments = path.segments.iter().map(|(_, s)| s);
        let id = segments.next().unwrap();
        let name = self.scopes[self.root_scope]
            .get(id.as_str())
            .ok_or_else(|| {
                new_error_with_span(
                    format!("undefined name `{id}`", id = id.as_str()),
                    state.document.path,
                    id.0,
                )
            })?;

        let mut current = id;
        let mut kind = name.kind;
        for segment in segments {
            let exports = match kind {
                ExternKind::Type(ExternType::Interface(id)) | ExternKind::Instance(id) => {
                    &self.definitions.interfaces[id].exports
                }
                ExternKind::Type(ExternType::World(id)) | ExternKind::Component(id) => {
                    &self.definitions.worlds[id].exports
                }
                _ => {
                    return Err(new_error_with_span(
                        format!(
                            "{kind} `{id}` has no exports",
                            kind = name.kind,
                            id = current.as_str()
                        ),
                        state.document.path,
                        current.0,
                    ))
                }
            };

            kind = exports
                .get(segment.as_str())
                .map(Extern::kind)
                .ok_or_else(|| {
                    new_error_with_span(
                        format!(
                            "{kind} `{id}` has no export named `{segment}`",
                            kind = name.kind,
                            id = current.as_str(),
                            segment = segment.as_str(),
                        ),
                        state.document.path,
                        current.0,
                    )
                })?;
            current = segment;
        }

        Ok(kind)
    }
}
