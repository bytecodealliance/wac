//! Module for resolving WAC documents.

use crate::ast::{self, new_error_with_span, serialize_span, Document, WorldIncludeStatement};
use anyhow::Result;
use id_arena::{Arena, Id};
use indexmap::{IndexMap, IndexSet};
use pest::Span;
use semver::Version;
use serde::{Serialize, Serializer};
use std::{
    collections::{HashMap, HashSet},
    fmt,
    path::{Path, PathBuf},
};

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

fn serialize_id_map<K, T, S>(
    map: &IndexMap<K, Id<T>>,
    serializer: S,
) -> std::result::Result<S::Ok, S::Error>
where
    K: Serialize,
    T: Serialize,
    S: Serializer,
{
    use serde::ser::SerializeMap;

    let mut s = serializer.serialize_map(Some(map.len()))?;
    for (k, v) in map {
        s.serialize_entry(k, &v.index())?;
    }
    s.end()
}

/// Represents information about a resolved package.
pub struct Package {
    /// The version of the package.
    pub version: Version,
    /// The bytes of the package.
    pub bytes: Vec<u8>,
}

/// A trait implemented by package resolvers.
///
/// This is used when resolving a document to resolve any referenced packages.
pub trait PackageResolver {
    /// Resolves a package by name.
    ///
    /// Returns `Ok(None)` if the package could not be found.
    fn resolve(&self, name: &ast::PackageName) -> Result<Option<Package>>;
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

impl PackageResolver for FileSystemPackageResolver {
    fn resolve(&self, name: &ast::PackageName) -> Result<Option<Package>> {
        // TODO: probe for a `<root>/<namespace>+/<name>.wasm` file which
        // may be an encoded WIT package or a component.
        // Also probe for a `<root>/<namespace>+/<name>` directory and
        // parse it as a textual WIT package, encoding it.
        todo!()
    }
}

/// An identifier for value types.
pub type ValueTypeId<'a> = Id<ValueType<'a>>;

/// An identifier for functions types.
pub type FuncTypeId<'a> = Id<FuncType<'a>>;

/// An identifier for interface types.
pub type InterfaceId<'a> = Id<InterfaceType<'a>>;

/// An identifier for world types.
pub type WorldId<'a> = Id<WorldType<'a>>;

/// An identifier for scopes.
pub type ScopeId<'a> = Id<Scope<'a>>;

/// Represents the kind of a name.
#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum NameKind<'a> {
    /// The name is an interface (i.e. instance type).
    Interface {
        /// The interface id.
        #[serde(serialize_with = "serialize_id")]
        id: InterfaceId<'a>,
        /// The interface's scope.
        #[serde(serialize_with = "serialize_id")]
        scope: ScopeId<'a>,
    },
    /// The name is a world (i.e. component type).
    World {
        /// The world id.
        #[serde(serialize_with = "serialize_id")]
        id: WorldId<'a>,
        /// The world's scope.
        #[serde(serialize_with = "serialize_id")]
        scope: ScopeId<'a>,
    },
    /// The name is a value type.
    Type(Type<'a>),
    /// The name is a function type.
    FuncType(#[serde(serialize_with = "serialize_id")] FuncTypeId<'a>),
    /// The name is an imported or aliased instance.
    Instance {
        /// The interface id.
        #[serde(serialize_with = "serialize_id")]
        id: InterfaceId<'a>,
        /// The interface's scope.
        #[serde(serialize_with = "serialize_id")]
        scope: ScopeId<'a>,
    },
    /// The name is an imported or aliased function.
    Func(#[serde(serialize_with = "serialize_id")] FuncTypeId<'a>),
}

impl fmt::Display for NameKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            NameKind::Interface { .. } => write!(f, "interface"),
            NameKind::World { .. } => write!(f, "world"),
            NameKind::Type(_) => write!(f, "value type"),
            NameKind::FuncType(_) => write!(f, "function type"),
            NameKind::Instance { .. } => write!(f, "instance"),
            NameKind::Func(_) => write!(f, "function"),
        }
    }
}

/// Represents a defined name.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Name<'a> {
    /// The span of the defining name.
    #[serde(serialize_with = "serialize_span")]
    pub span: Span<'a>,
    /// The kind of name.
    pub kind: NameKind<'a>,
}

/// Represents a scope for names.
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "camelCase")]

pub struct Scope<'a> {
    #[serde(serialize_with = "serialize_optional_id")]
    parent: Option<ScopeId<'a>>,
    names: IndexMap<&'a str, Name<'a>>,
}

impl<'a> Scope<'a> {
    /// Gets a name from the scope.
    pub fn get(&self, name: &str) -> Option<&Name<'a>> {
        self.names.get(name)
    }

    /// Iterates all names in the scope.
    pub fn iter(&self) -> impl Iterator<Item = &Name<'a>> {
        self.names.values()
    }
}

/// Represents a resolved document.
///
/// A resolution may be encoded to a WebAssembly component.
#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ResolvedDocument<'a> {
    /// The document being resolved.
    #[serde(skip)]
    pub document: &'a Document<'a>,
    /// The name of the package being resolved.
    pub package: String,
    /// The value types in the resolution.
    #[serde(serialize_with = "serialize_arena")]
    pub types: Arena<ValueType<'a>>,
    /// The function types in the resolution.
    #[serde(serialize_with = "serialize_arena")]
    pub funcs: Arena<FuncType<'a>>,
    /// The interface types in the resolution.
    #[serde(serialize_with = "serialize_arena")]
    pub interfaces: Arena<InterfaceType<'a>>,
    /// The world types in the resolution.
    #[serde(serialize_with = "serialize_arena")]
    pub worlds: Arena<WorldType<'a>>,
    /// The name scopes in the resolution.
    #[serde(serialize_with = "serialize_arena")]
    pub scopes: Arena<Scope<'a>>,
    #[serde(skip)]
    root_scope: ScopeId<'a>,
    #[serde(skip)]
    current_scope: ScopeId<'a>,
}

impl<'a> ResolvedDocument<'a> {
    /// Creates a new resolved document from the given document.
    pub fn new(
        document: &'a ast::Document<'a>,
        package: impl Into<String>,
        resolver: Option<Box<dyn PackageResolver>>,
    ) -> Result<Self> {
        let mut scopes = Arena::new();
        let root_scope = scopes.alloc(Scope {
            parent: None,
            names: Default::default(),
        });

        let mut resolution = Self {
            document,
            package: package.into(),
            types: Default::default(),
            funcs: Default::default(),
            interfaces: Default::default(),
            worlds: Default::default(),
            scopes,
            root_scope,
            current_scope: root_scope,
        };

        for stmt in &document.statements {
            match &stmt.stmt {
                ast::Statement::Import(i) => resolution.import(i)?,
                ast::Statement::Type(t) => resolution.type_statement(t)?,
                ast::Statement::Let(_) => todo!("implement let statements"),
                ast::Statement::Export(_) => todo!("implement export statements"),
            }
        }

        Ok(resolution)
    }

    /// Gets the root name scope of the resolution.
    pub fn root(&self) -> &Scope {
        &self.scopes[self.root_scope]
    }

    /// Encode the resolved document as a WebAssembly component.
    pub fn encode(&self) -> Result<Vec<u8>> {
        todo!("implement encoding")
    }

    fn get(&self, id: &ast::Ident) -> Option<&Name<'a>> {
        let mut current = &self.scopes[self.current_scope];
        loop {
            if let Some(name) = current.get(id.as_str()) {
                return Some(name);
            }

            current = &self.scopes[current.parent?];
        }
    }

    fn require(&self, id: &ast::Ident) -> Result<&Name<'a>> {
        self.get(id).ok_or_else(|| {
            new_error_with_span(format!("undefined name `{id}`"), self.document.path, id.0)
        })
    }

    fn push_scope(&mut self) {
        self.current_scope = self.scopes.alloc(Scope {
            parent: Some(self.current_scope),
            names: Default::default(),
        });
    }

    fn pop_scope(&mut self) -> ScopeId<'a> {
        let id = self.current_scope;
        self.current_scope = self.scopes[self.current_scope]
            .parent
            .expect("expected a scope to pop");
        id
    }

    fn register_name(&mut self, id: ast::Ident<'a>, kind: NameKind<'a>) -> Result<()> {
        if let Some(prev) = self.scopes[self.current_scope]
            .names
            .insert(id.as_str(), Name { span: id.0, kind })
        {
            let (line, column) = prev.span.start_pos().line_col();
            return Err(new_error_with_span(
                format!(
                    "`{id}` was previously defined at {path}:{line}:{column}",
                    path = self.document.path.display(),
                ),
                self.document.path,
                id.0,
            ));
        }

        Ok(())
    }

    fn import(&mut self, stmt: &'a ast::ImportStatement<'a>) -> Result<()> {
        let kind = match &stmt.ty {
            ast::ImportType::Package(_) => todo!("implement package resolution"),
            ast::ImportType::Func(ty) => NameKind::Func(self.func_type(ty)?),
            ast::ImportType::Interface(i) => {
                let mut ty = InterfaceType {
                    kind: InterfaceKind::Inline(i),
                    types: Default::default(),
                    exports: Default::default(),
                };

                self.push_scope();
                self.interface_body(None, &i.body, &mut ty)?;
                let scope = self.pop_scope();

                let id = self.interfaces.alloc(ty);
                NameKind::Instance { id, scope }
            }
            ast::ImportType::Ident(id) => {
                let name = self.require(id)?;
                match &name.kind {
                    NameKind::FuncType(id) => NameKind::Func(*id),
                    NameKind::Interface { id, scope } => NameKind::Instance {
                        id: *id,
                        scope: *scope,
                    },
                    _ => {
                        return Err(new_error_with_span(
                            format!(
                                "{kind} `{id}` is not an interface or function type",
                                kind = name.kind
                            ),
                            self.document.path,
                            id.0,
                        ))
                    }
                }
            }
        };

        self.register_name(stmt.id, kind)
    }

    fn type_statement(&mut self, stmt: &'a ast::TypeStatement) -> Result<()> {
        match stmt {
            ast::TypeStatement::Interface(i) => self.interface_decl(i),
            ast::TypeStatement::World(w) => self.world_decl(w),
            ast::TypeStatement::Type(t) => self.type_decl(t).map(|_| ()),
        }
    }

    fn interface_decl(&mut self, decl: &'a ast::InterfaceDecl<'a>) -> Result<()> {
        let mut ty = InterfaceType {
            kind: InterfaceKind::Declared {
                decl,
                id: format!("{pkg}/{iface}", pkg = self.package, iface = decl.id),
            },
            types: Default::default(),
            exports: Default::default(),
        };

        self.push_scope();
        self.interface_body(Some(decl.id.as_str()), &decl.body, &mut ty)?;
        let scope = self.pop_scope();

        let id = self.interfaces.alloc(ty);

        self.register_name(decl.id, NameKind::Interface { id, scope })
    }

    fn world_decl(&mut self, decl: &'a ast::WorldDecl<'a>) -> Result<()> {
        let mut ty = WorldType {
            decl,
            types: Default::default(),
            imports: Default::default(),
            exports: Default::default(),
        };

        self.push_scope();
        self.world_body(&decl.body, &mut ty)?;
        let scope = self.pop_scope();

        let id = self.worlds.alloc(ty);

        self.register_name(decl.id, NameKind::World { id, scope })
    }

    fn interface_body(
        &mut self,
        name: Option<&str>,
        body: &'a ast::InterfaceBody<'a>,
        ty: &mut InterfaceType<'a>,
    ) -> Result<()> {
        for item in &body.items {
            match &item.stmt {
                ast::InterfaceItemStatement::Use(u) => self.use_type(u, &mut ty.types)?,
                ast::InterfaceItemStatement::Type(decl) => {
                    let prev = ty.types.insert(decl.id().as_str(), self.type_decl(decl)?);
                    assert!(prev.is_none(), "duplicate type in scope");
                }
                ast::InterfaceItemStatement::Export(e) => {
                    if ty
                        .exports
                        .insert(e.id.as_str(), self.func_type_ref(&e.ty)?)
                        .is_some()
                    {
                        return Err(new_error_with_span(
                            match name {
                                Some(name) => format!(
                                    "duplicate interface export `{id}` for interface `{name}`",
                                    id = e.id
                                ),
                                None => format!("duplicate interface export `{id}`", id = e.id),
                            },
                            self.document.path,
                            e.id.0,
                        ));
                    }
                }
            }
        }

        Ok(())
    }

    fn world_body(&mut self, body: &'a ast::WorldBody<'a>, ty: &mut WorldType<'a>) -> Result<()> {
        let mut includes = Vec::new();
        for item in &body.items {
            match &item.stmt {
                ast::WorldItemStatement::Use(u) => self.use_type(u, &mut ty.types)?,
                ast::WorldItemStatement::Type(decl) => {
                    let prev = ty.types.insert(decl.id().as_str(), self.type_decl(decl)?);
                    assert!(prev.is_none(), "duplicate type in scope");
                }
                ast::WorldItemStatement::Import(i) => self.world_item_decl(&i.decl, true, ty)?,
                ast::WorldItemStatement::Export(e) => self.world_item_decl(&e.decl, false, ty)?,
                ast::WorldItemStatement::Include(i) => {
                    // We delay processing includes until after all other items have been processed
                    includes.push(i);
                }
            }
        }

        // Process the includes now that all imports and exports have been processed.
        // This allows us to detect conflicts only in explicitly defined items.
        for i in includes {
            self.world_include(i, ty)?;
        }

        Ok(())
    }

    fn world_item_decl(
        &mut self,
        decl: &'a ast::WorldItemDecl<'a>,
        import: bool,
        ty: &mut WorldType<'a>,
    ) -> Result<()> {
        let check_name = |name: &str, span: Span, ty: &mut WorldType| {
            for (desc, map) in [("import", &ty.imports), ("export", &ty.exports)] {
                if map.contains_key(name) {
                    return Err(new_error_with_span(
                            format!(
                                "{dir} `{name}` conflicts with existing {desc} of the same name in world `{world}`",
                                dir = if import { "import" } else { "export" },
                                world = ty.decl.id,
                            ),
                            self.document.path,
                            span,
                        ));
                }
            }

            Ok(())
        };

        let (name, item) = match decl {
            ast::WorldItemDecl::Named(named) => {
                check_name(named.id.as_str(), named.id.0, ty)?;

                (
                    ExternName::Kebab(named.id.as_str().to_string()),
                    match &named.ty {
                        ast::ExternType::Ident(id) => {
                            let name = self.require(id)?;
                            match &name.kind {
                                NameKind::Interface { id, scope } => WorldItemType::Interface {
                                    id: *id,
                                    scope: *scope,
                                },
                                NameKind::FuncType(id) => WorldItemType::Func(*id),
                                _ => {
                                    return Err(new_error_with_span(
                                        format!(
                                            "{kind} `{id}` is not a function type or interface",
                                            kind = name.kind,
                                        ),
                                        self.document.path,
                                        id.0,
                                    ))
                                }
                            }
                        }
                        ast::ExternType::Func(f) => WorldItemType::Func(self.func_type(f)?),
                        ast::ExternType::Interface(i) => {
                            let mut ty = InterfaceType {
                                kind: InterfaceKind::Inline(i),
                                types: Default::default(),
                                exports: Default::default(),
                            };

                            self.push_scope();
                            self.interface_body(None, &i.body, &mut ty)?;
                            let scope = self.pop_scope();

                            WorldItemType::Interface {
                                id: self.interfaces.alloc(ty),
                                scope,
                            }
                        }
                    },
                )
            }
            ast::WorldItemDecl::Interface(i) => match i {
                ast::InterfaceRef::Ident(id) => {
                    let name = self.require(id)?;
                    match &name.kind {
                        NameKind::Interface { id: iface, scope } => {
                            let name = match &self.interfaces[*iface].kind {
                                InterfaceKind::Declared { id: iface_id, .. } => {
                                    check_name(iface_id.as_str(), id.0, ty)?;
                                    ExternName::Interface(iface_id.clone())
                                }
                                _ => unreachable!("reference cannot be to an inline interface"),
                            };
                            (
                                name,
                                WorldItemType::Interface {
                                    id: *iface,
                                    scope: *scope,
                                },
                            )
                        }
                        _ => {
                            return Err(new_error_with_span(
                                format!("{kind} `{id}` is not an interface", kind = name.kind),
                                self.document.path,
                                id.0,
                            ))
                        }
                    }
                }
                ast::InterfaceRef::Path(_) => todo!("implement package resolution"),
            },
        };

        if import {
            ty.imports.insert(name, item);
        } else {
            ty.exports.insert(name, item);
        }

        Ok(())
    }

    fn world_include(
        &mut self,
        stmt: &ast::WorldIncludeStatement<'a>,
        ty: &mut WorldType<'a>,
    ) -> Result<()> {
        let id = match &stmt.world {
            ast::WorldRef::Ident(id) => {
                let name = self.require(id)?;
                match name.kind {
                    NameKind::World { id, .. } => id,
                    _ => {
                        return Err(new_error_with_span(
                            format!("{kind} `{id}` is not a world", kind = name.kind),
                            self.document.path,
                            id.0,
                        ))
                    }
                }
            }
            ast::WorldRef::Path(_) => todo!("implement package resolution"),
        };

        let other = &self.worlds[id];
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
                    self.document.path,
                    item.name.0,
                ));
            }
        }

        for (name, item) in &other.imports {
            insert(
                stmt,
                ty,
                name,
                item,
                true,
                &mut replacements,
                self.document.path,
            )?;
        }

        for (name, item) in &other.exports {
            insert(
                stmt,
                ty,
                name,
                item,
                false,
                &mut replacements,
                self.document.path,
            )?;
        }

        if let Some(missing) = replacements.values().next() {
            return Err(new_error_with_span(
                format!(
                    "world `{other}` does not have an import or export with kebab-name `{name}`",
                    other = stmt.world.name(),
                    name = missing.name.as_str(),
                ),
                self.document.path,
                missing.name.0,
            ));
        }

        return Ok(());

        fn insert<'a>(
            stmt: &WorldIncludeStatement<'a>,
            ty: &mut WorldType<'a>,
            name: &ExternName,
            item: &WorldItemType<'a>,
            import: bool,
            replacements: &mut HashMap<&'a str, &ast::WorldIncludeItem<'a>>,
            path: &Path,
        ) -> Result<()> {
            let name = match name {
                ExternName::Kebab(name) => {
                    let (name, span) = replacements
                        .remove(name.as_str())
                        .map(|r| (r.other.as_str(), r.other.0))
                        .unwrap_or_else(|| (name.as_str(), stmt.world.span()));
                    for (desc, map) in [("import", &ty.imports), ("export", &ty.exports)] {
                        if map.contains_key(name) {
                            return Err(new_error_with_span(
                                format!(
                                    "{dir} `{name}` from world `{other}` conflicts with {desc} of the same name in world `{world}`{hint}",
                                    dir = if import { "import" } else { "export" },
                                    other = stmt.world.name(),
                                    world = ty.decl.id,
                                    hint = if stmt.with.is_some() { "" } else {
                                        " (consider using a `with` clause to use a different name)"
                                    }
                                ),
                                path,
                                span,
                            ));
                        }
                    }

                    ExternName::Kebab(name.to_string())
                }
                ExternName::Interface(i) => ExternName::Interface(i.clone()),
            };

            if let Some(prev) = if import {
                ty.imports.insert(name, *item)
            } else {
                ty.exports.insert(name, *item)
            } {
                assert_eq!(prev, *item);
            }

            Ok(())
        }
    }

    fn use_type(
        &mut self,
        stmt: &'a ast::UseStatement,
        types: &mut IndexMap<&'a str, LocalType<'a>>,
    ) -> Result<()> {
        match &stmt.items.path {
            ast::UsePath::Package(_) => todo!("implement package resolution"),
            ast::UsePath::Ident(id) => {
                let name = self.require(id)?;
                match name.kind {
                    NameKind::Interface { scope, .. } => {
                        for item in &stmt.items.list {
                            let name = self.scopes[scope].get(item.as_str()).ok_or_else(|| {
                                new_error_with_span(
                                    format!("type `{item}` is not defined in interface `{id}`"),
                                    self.document.path,
                                    item.0,
                                )
                            })?;

                            let prev = types.insert(
                                item.as_str(),
                                match &name.kind {
                                    NameKind::Type(ty) => LocalType::Type(*ty),
                                    NameKind::FuncType(id) => LocalType::FuncType(*id),
                                    _ => unreachable!("invalid name in interface scope"),
                                },
                            );
                            assert!(prev.is_none(), "duplicate type in scope");
                            self.register_name(*item, name.kind)?;
                        }

                        Ok(())
                    }
                    _ => Err(new_error_with_span(
                        format!("`{id}` is not an interface"),
                        self.document.path,
                        id.0,
                    )),
                }
            }
        }
    }

    fn type_decl(&mut self, decl: &'a ast::TypeDecl<'a>) -> Result<LocalType<'a>> {
        match decl {
            ast::TypeDecl::Resource(r) => self.resource_decl(r),
            ast::TypeDecl::Variant(v) => self.variant_decl(v),
            ast::TypeDecl::Record(r) => self.record_decl(r),
            ast::TypeDecl::Flags(f) => self.flags_decl(f),
            ast::TypeDecl::Enum(e) => self.enum_decl(e),
            ast::TypeDecl::Alias(a) => self.type_alias(a),
        }
    }

    fn resource_decl(&mut self, decl: &'a ast::ResourceDecl<'a>) -> Result<LocalType<'a>> {
        let methods = match &decl.body {
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
                                    self.document.path,
                                    keyword.0,
                                ));
                            }

                            constructor = true;
                            let mut names = HashSet::new();

                            Ok(ResourceMethodType::Constructor(
                                params
                                    .list
                                    .iter()
                                    .map(|p| {
                                        if !names.insert(p.id.as_str()) {
                                            return Err(new_error_with_span(
                                                format!(
                                                    "duplicate constructor parameter `{id}` for resource `{res}`",
                                                    id = p.id,
                                                    res = decl.id
                                                ),
                                                self.document.path,
                                                p.id.0,
                                            ));
                                        }

                                        self.ty(&p.ty)
                                    })
                                    .collect::<Result<_>>()?,
                            ))
                        }
                        ast::ResourceMethod::Method(ast::Method {
                            id, func, keyword, ..
                        }) => {
                            if !names.insert(id.as_str()) {
                                return Err(new_error_with_span(
                                    format!(
                                        "duplicate method `{id}` for resource `{res}`",
                                        res = decl.id
                                    ),
                                    self.document.path,
                                    id.0,
                                ));
                            }

                            if keyword.is_some() {
                                Ok(ResourceMethodType::Static {
                                    name: id.as_str(),
                                    ty: self.func_type_ref(func)?,
                            })
                            } else {
                                Ok(ResourceMethodType::Instance {
                                    name: id.as_str(),
                                    ty: self.func_type_ref(func)?,
                                })
                            }
                        }
                    })
                    .collect::<Result<_>>()?
            }
        };

        let ty = Type::Id(
            self.types
                .alloc(ValueType::Resource(ResourceType { decl, methods })),
        );

        self.register_name(decl.id, NameKind::Type(ty))?;
        Ok(LocalType::Type(ty))
    }

    fn variant_decl(&mut self, decl: &'a ast::VariantDecl) -> Result<LocalType<'a>> {
        let mut cases = IndexMap::new();
        for case in &decl.body.cases {
            if cases
                .insert(
                    case.id.as_str(),
                    case.ty.as_ref().map(|t| self.ty(&t.ty)).transpose()?,
                )
                .is_some()
            {
                return Err(new_error_with_span(
                    format!(
                        "duplicate case `{case}` for variant type `{ty}`",
                        case = case.id,
                        ty = decl.id
                    ),
                    self.document.path,
                    case.id.0,
                ));
            }
        }

        let ty = Type::Id(
            self.types
                .alloc(ValueType::Variant(VariantType { decl, cases })),
        );

        self.register_name(decl.id, NameKind::Type(ty))?;
        Ok(LocalType::Type(ty))
    }

    fn record_decl(&mut self, decl: &'a ast::RecordDecl<'a>) -> Result<LocalType<'a>> {
        let mut fields = IndexMap::new();
        for field in &decl.body.fields {
            if fields
                .insert(field.id.as_str(), self.ty(&field.ty)?)
                .is_some()
            {
                return Err(new_error_with_span(
                    format!(
                        "duplicate field `{field}` for record type `{ty}`",
                        field = field.id,
                        ty = decl.id
                    ),
                    self.document.path,
                    field.id.0,
                ));
            }
        }

        let ty = Type::Id(
            self.types
                .alloc(ValueType::Record(RecordType { decl, fields })),
        );

        self.register_name(decl.id, NameKind::Type(ty))?;
        Ok(LocalType::Type(ty))
    }

    fn flags_decl(&mut self, decl: &'a ast::FlagsDecl<'a>) -> Result<LocalType<'a>> {
        let mut flags = IndexSet::new();
        for flag in &decl.body.flags {
            if !flags.insert(flag.as_str()) {
                return Err(new_error_with_span(
                    format!(
                        "duplicate flag `{flag}` for flags type `{ty}`",
                        ty = decl.id
                    ),
                    self.document.path,
                    flag.0,
                ));
            }
        }

        let ty = Type::Id(
            self.types
                .alloc(ValueType::Flags(FlagsType { decl, flags })),
        );

        self.register_name(decl.id, NameKind::Type(ty))?;
        Ok(LocalType::Type(ty))
    }

    fn enum_decl(&mut self, decl: &'a ast::EnumDecl<'a>) -> Result<LocalType<'a>> {
        let mut cases = IndexSet::new();
        for case in &decl.body.cases {
            if !cases.insert(case.as_str()) {
                return Err(new_error_with_span(
                    format!("duplicate case `{case}` for enum type `{ty}`", ty = decl.id),
                    self.document.path,
                    case.0,
                ));
            }
        }

        let ty = Type::Id(self.types.alloc(ValueType::Enum(EnumType { decl, cases })));
        self.register_name(decl.id, NameKind::Type(ty))?;
        Ok(LocalType::Type(ty))
    }

    fn type_alias(&mut self, alias: &'a ast::TypeAlias<'a>) -> Result<LocalType<'a>> {
        let (kind, ty) = match &alias.kind {
            ast::TypeAliasKind::Func(f) => {
                let id = self.func_type(f)?;
                (NameKind::FuncType(id), LocalType::FuncType(id))
            }
            ast::TypeAliasKind::Type(ty) => match ty {
                ast::Type::Ident(id) => {
                    let name = self.require(id)?;
                    match &name.kind {
                        NameKind::Type(ty) => {
                            let id = self
                                .types
                                .alloc(ValueType::Alias(ValueTypeAlias { alias, ty: *ty }));
                            (NameKind::Type(Type::Id(id)), LocalType::Type(Type::Id(id)))
                        }
                        NameKind::FuncType(id) => {
                            (NameKind::FuncType(*id), LocalType::FuncType(*id))
                        }
                        _ => {
                            return Err(new_error_with_span(
                                format!(
                                    "{kind} `{id}` cannot be used in a type alias",
                                    kind = name.kind
                                ),
                                self.document.path,
                                id.0,
                            ))
                        }
                    }
                }
                _ => {
                    let ty = self.ty(ty)?;
                    let id = self
                        .types
                        .alloc(ValueType::Alias(ValueTypeAlias { alias, ty }));
                    (NameKind::Type(Type::Id(id)), LocalType::Type(Type::Id(id)))
                }
            },
        };

        self.register_name(alias.id, kind)?;
        Ok(ty)
    }

    fn func_type_ref(&mut self, r: &'a ast::FuncTypeRef<'a>) -> Result<FuncTypeId<'a>> {
        match r {
            ast::FuncTypeRef::Func(ty) => self.func_type(ty),
            ast::FuncTypeRef::Ident(id) => {
                let name = self.require(id)?;
                match &name.kind {
                    NameKind::FuncType(id) => Ok(*id),
                    _ => Err(new_error_with_span(
                        format!("{kind} `{id}` is not a function type", kind = name.kind),
                        self.document.path,
                        id.0,
                    )),
                }
            }
        }
    }

    fn ty(&mut self, ty: &'a ast::Type<'a>) -> Result<Type<'a>> {
        match ty {
            ast::Type::U8(_) => Ok(Type::U8),
            ast::Type::S8(_) => Ok(Type::S8),
            ast::Type::U16(_) => Ok(Type::U16),
            ast::Type::S16(_) => Ok(Type::S16),
            ast::Type::U32(_) => Ok(Type::U32),
            ast::Type::S32(_) => Ok(Type::S32),
            ast::Type::U64(_) => Ok(Type::U64),
            ast::Type::S64(_) => Ok(Type::S64),
            ast::Type::Float32(_) => Ok(Type::Float32),
            ast::Type::Float64(_) => Ok(Type::Float64),
            ast::Type::Char(_) => Ok(Type::Char),
            ast::Type::Bool(_) => Ok(Type::Bool),
            ast::Type::String(_) => Ok(Type::String),
            ast::Type::Tuple(v) => {
                let types = v
                    .types
                    .iter()
                    .map(|ty| self.ty(ty))
                    .collect::<Result<_>>()?;

                Ok(Type::Id(self.types.alloc(ValueType::Tuple(types))))
            }
            ast::Type::List(l) => {
                let ty = self.ty(&l.ty)?;
                Ok(Type::Id(self.types.alloc(ValueType::List(ty))))
            }
            ast::Type::Option(o) => {
                let ty = self.ty(&o.ty)?;
                Ok(Type::Id(self.types.alloc(ValueType::Option(ty))))
            }
            ast::Type::Result(r) => {
                let (ok, err) = match &r.specified {
                    Some(s) => {
                        let ok = match &s.ok {
                            ast::OmitType::Omitted(_) => None,
                            ast::OmitType::Type(t) => Some(self.ty(t)?),
                        };

                        let err = s.err.as_ref().map(|t| self.ty(t)).transpose()?;
                        (ok, err)
                    }
                    None => (None, None),
                };

                Ok(Type::Id(self.types.alloc(ValueType::Result { ok, err })))
            }
            ast::Type::Borrow(b) => {
                let name = self.require(&b.id)?;
                if let NameKind::Type(Type::Id(id)) = &name.kind {
                    if let ValueType::Resource(_) = &self.types[*id] {
                        return Ok(Type::Id(self.types.alloc(ValueType::Borrow(*id))));
                    }
                }

                Err(new_error_with_span(
                    format!(
                        "{kind} `{id}` is not a resource type",
                        kind = name.kind,
                        id = b.id
                    ),
                    self.document.path,
                    b.id.0,
                ))
            }
            ast::Type::Ident(id) => {
                let name = self.require(id)?;
                match &name.kind {
                    NameKind::Type(ty) => Ok(*ty),
                    _ => Err(new_error_with_span(
                        format!(
                            "{kind} `{id}` cannot be used as a value type",
                            kind = name.kind
                        ),
                        self.document.path,
                        id.0,
                    )),
                }
            }
        }
    }

    fn func_type(&mut self, func: &'a ast::FuncType<'a>) -> Result<FuncTypeId<'a>> {
        let mut params = IndexMap::new();
        for param in &func.params.list {
            if params
                .insert(param.id.as_str(), self.ty(&param.ty)?)
                .is_some()
            {
                return Err(new_error_with_span(
                    format!("duplicate function parameter `{id}`", id = param.id),
                    self.document.path,
                    param.id.0,
                ));
            }
        }

        let results = func
            .results
            .as_ref()
            .map(|r| match r {
                ast::ResultList::Named { results: r, .. } => {
                    let mut results = IndexMap::new();
                    for result in &r.list {
                        if results
                            .insert(result.id.as_str(), self.ty(&result.ty)?)
                            .is_some()
                        {
                            return Err(new_error_with_span(
                                format!("duplicate function result `{id}`", id = result.id),
                                self.document.path,
                                result.id.0,
                            ));
                        }
                    }
                    Ok(ResultList::Named(results))
                }
                ast::ResultList::Single { ty, .. } => Ok(ResultList::Single(self.ty(ty)?)),
            })
            .transpose()?;

        Ok(self.funcs.alloc(FuncType {
            decl: func,
            params,
            results,
        }))
    }
}
