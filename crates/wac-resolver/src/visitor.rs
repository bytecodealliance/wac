use miette::SourceSpan;
use semver::Version;
use wac_parser::ast::{
    Document, Expr, ExternType, ImportStatement, ImportType, InstantiationArgument, InterfaceItem,
    PrimaryExpr, Statement, TypeStatement, UsePath, WorldItem, WorldItemPath, WorldRef,
};

use crate::Error;

/// A visitor of packages referenced in a document.
///
/// This can be used to collect all of the packages referenced
/// in a document so that they may all be resolved at the same time.
pub struct PackageVisitor<T>(T);

impl<'a, T> PackageVisitor<T>
where
    T: FnMut(&'a str, Option<&'a Version>, SourceSpan) -> bool,
{
    /// Creates a new package visitor with the given callback.
    ///
    /// The callback receives the package name, optional version, and
    /// the span of the package name.
    pub fn new(cb: T) -> Self {
        Self(cb)
    }

    /// Visits any package names referenced in the document.
    ///
    /// The package names are visited in-order and will not deduplicate
    /// names/versions that are referenced multiple times.
    pub fn visit(&mut self, doc: &'a Document) -> Result<(), Error> {
        if let Some(targets) = &doc.directive.targets {
            if !(self.0)(
                targets.name,
                targets.version.as_ref(),
                targets.package_name_span(),
            ) {
                return Ok(());
            }
        }

        for stmt in &doc.statements {
            match stmt {
                Statement::Import(i) => {
                    if !self.import_statement(i) {
                        break;
                    }
                }
                Statement::Type(t) => {
                    if !self.type_statement(t) {
                        break;
                    }
                }
                Statement::Let(l) => {
                    if !self.expr(doc.directive.package.name, &l.expr)? {
                        break;
                    }
                }
                Statement::Export(e) => {
                    if !self.expr(doc.directive.package.name, &e.expr)? {
                        break;
                    }
                }
            }
        }

        Ok(())
    }

    fn import_statement(&mut self, stmt: &'a ImportStatement) -> bool {
        match &stmt.ty {
            ImportType::Package(p) => (self.0)(p.name, p.version.as_ref(), p.package_name_span()),
            ImportType::Interface(i) => {
                for item in &i.items {
                    if !self.interface_item(item) {
                        return false;
                    }
                }

                true
            }
            ImportType::Func(_) | ImportType::Ident(_) => true,
        }
    }

    fn type_statement(&mut self, stmt: &'a TypeStatement) -> bool {
        match stmt {
            TypeStatement::Interface(i) => {
                for item in &i.items {
                    if !self.interface_item(item) {
                        return false;
                    }
                }

                true
            }
            TypeStatement::World(w) => {
                for item in &w.items {
                    if !self.world_item(item) {
                        return false;
                    }
                }

                true
            }
            TypeStatement::Type(_) => true,
        }
    }

    fn interface_item(&mut self, item: &'a InterfaceItem) -> bool {
        match item {
            InterfaceItem::Use(u) => match &u.path {
                UsePath::Package(p) => (self.0)(p.name, p.version.as_ref(), p.package_name_span()),
                UsePath::Ident(_) => true,
            },
            InterfaceItem::Type(_) | InterfaceItem::Export(_) => true,
        }
    }

    fn world_item(&mut self, item: &'a WorldItem) -> bool {
        match item {
            WorldItem::Use(u) => match &u.path {
                UsePath::Package(p) => (self.0)(p.name, p.version.as_ref(), p.package_name_span()),
                UsePath::Ident(_) => true,
            },
            WorldItem::Type(_) => true,
            WorldItem::Import(i) => self.world_item_path(&i.path),
            WorldItem::Export(e) => self.world_item_path(&e.path),
            WorldItem::Include(i) => match &i.world {
                WorldRef::Package(p) => (self.0)(p.name, p.version.as_ref(), p.package_name_span()),
                WorldRef::Ident(_) => true,
            },
        }
    }

    fn world_item_path(&mut self, path: &'a WorldItemPath) -> bool {
        match path {
            WorldItemPath::Named(n) => match &n.ty {
                ExternType::Interface(i) => {
                    for item in &i.items {
                        if !self.interface_item(item) {
                            return false;
                        }
                    }

                    true
                }
                ExternType::Ident(_) | ExternType::Func(_) => true,
            },
            WorldItemPath::Package(p) => {
                (self.0)(p.name, p.version.as_ref(), p.package_name_span())
            }
            WorldItemPath::Ident(_) => true,
        }
    }

    fn expr(&mut self, this: &str, expr: &'a Expr) -> Result<bool, Error> {
        match &expr.primary {
            PrimaryExpr::New(e) => {
                if e.package.name == this {
                    return Err(Error::CannotInstantiateSelf {
                        span: e.package.span,
                    });
                }

                if !(self.0)(e.package.name, e.package.version.as_ref(), e.package.span) {
                    return Ok(false);
                }

                for arg in &e.arguments {
                    match arg {
                        InstantiationArgument::Inferred(_)
                        | InstantiationArgument::Spread(_)
                        | InstantiationArgument::Fill(_) => continue,
                        InstantiationArgument::Named(a) => {
                            if !self.expr(this, &a.expr)? {
                                return Ok(false);
                            }
                        }
                    }
                }

                Ok(true)
            }
            PrimaryExpr::Nested(e) => self.expr(this, &e.inner),
            PrimaryExpr::Ident(_) => Ok(true),
        }
    }
}
