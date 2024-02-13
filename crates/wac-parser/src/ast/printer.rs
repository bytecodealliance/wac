//! Module for printing WAC documents.

use crate::ast::*;
use std::fmt::Write;

/// A printer for WAC documents.
pub struct DocumentPrinter<'a, W: Write> {
    writer: W,
    source: &'a str,
    space: &'static str,
    indent: usize,
    indented: bool,
}

impl<'a, W: Write> DocumentPrinter<'a, W> {
    /// Creates a new document printer for the given write.
    ///
    /// If `space` is `None`, then the printer will use four spaces for
    /// indentation.
    pub fn new(writer: W, source: &'a str, space: Option<&'static str>) -> Self {
        Self {
            writer,
            source,
            space: space.unwrap_or("    "),
            indent: 0,
            indented: false,
        }
    }

    /// Prints the given document.
    pub fn document(&mut self, doc: &Document) -> std::fmt::Result {
        self.docs(&doc.docs)?;
        self.package_directive(&doc.directive)?;

        for (i, statement) in doc.statements.iter().enumerate() {
            if i > 0 {
                self.newline()?;
            }

            self.statement(statement)?;
            self.newline()?;
        }

        Ok(())
    }

    /// Prints the given package directive.
    pub fn package_directive(&mut self, directive: &PackageDirective) -> std::fmt::Result {
        self.indent()?;
        write!(
            self.writer,
            "package {package}",
            package = self.source(directive.package.span),
        )?;

        if let Some(targets) = &directive.targets {
            write!(self.writer, " ")?;
            self.package_path(targets)?;
        }

        writeln!(self.writer, ";")?;
        self.newline()
    }

    /// Prints the given statement.
    pub fn statement(&mut self, statement: &Statement) -> std::fmt::Result {
        match statement {
            Statement::Import(i) => self.import_statement(i),
            Statement::Type(t) => self.type_statement(t),
            Statement::Let(l) => self.let_statement(l),
            Statement::Export(e) => self.export_statement(e),
        }
    }

    /// Prints the given doc comments.
    pub fn docs(&mut self, docs: &[DocComment]) -> std::fmt::Result {
        for doc in docs {
            for line in doc.comment.lines() {
                self.indent()?;
                write!(self.writer, "/// {line}", line = line.trim())?;
                self.newline()?;
            }
        }

        Ok(())
    }

    /// Prints the given import statement.
    pub fn import_statement(&mut self, statement: &ImportStatement) -> std::fmt::Result {
        self.docs(&statement.docs)?;

        self.indent()?;
        write!(
            self.writer,
            "import {id}",
            id = self.source(statement.id.span)
        )?;

        if let Some(name) = &statement.name {
            write!(self.writer, " as {name}", name = self.source(name.span()))?;
        }

        write!(self.writer, ": ")?;
        self.import_type(&statement.ty)?;
        write!(self.writer, ";")?;

        Ok(())
    }

    /// Prints the given import type.
    pub fn import_type(&mut self, ty: &ImportType) -> std::fmt::Result {
        match ty {
            ImportType::Package(p) => self.package_path(p),
            ImportType::Func(f) => self.func_type(f),
            ImportType::Interface(i) => self.inline_interface(i),
            ImportType::Ident(id) => write!(self.writer, "{id}", id = self.source(id.span)),
        }
    }

    /// Prints the given package path.
    pub fn package_path(&mut self, path: &PackagePath) -> std::fmt::Result {
        write!(self.writer, "{path}", path = self.source(path.span))?;
        Ok(())
    }

    /// Prints the given function type.
    pub fn func_type(&mut self, ty: &FuncType) -> std::fmt::Result {
        write!(self.writer, "func(")?;
        self.named_types(&ty.params)?;
        write!(self.writer, ")")?;

        match &ty.results {
            ResultList::Empty => Ok(()),
            ResultList::Scalar(ty) => {
                write!(self.writer, " -> ")?;
                self.ty(ty)
            }
            ResultList::Named(results) => {
                write!(self.writer, " -> (")?;
                self.named_types(results)?;
                write!(self.writer, ")")
            }
        }
    }

    fn named_types(&mut self, types: &[NamedType]) -> std::fmt::Result {
        for (i, param) in types.iter().enumerate() {
            if i > 0 {
                write!(self.writer, ", ")?;
            }

            write!(self.writer, "{id}: ", id = self.source(param.id.span))?;
            self.ty(&param.ty)?;
        }

        Ok(())
    }

    /// Prints the given type.
    pub fn ty(&mut self, ty: &Type) -> std::fmt::Result {
        match ty {
            Type::U8(_) => write!(self.writer, "u8"),
            Type::S8(_) => write!(self.writer, "s8"),
            Type::U16(_) => write!(self.writer, "u16"),
            Type::S16(_) => write!(self.writer, "s16"),
            Type::U32(_) => write!(self.writer, "u32"),
            Type::S32(_) => write!(self.writer, "s32"),
            Type::U64(_) => write!(self.writer, "u64"),
            Type::S64(_) => write!(self.writer, "s64"),
            Type::Float32(_) => write!(self.writer, "float32"),
            Type::Float64(_) => write!(self.writer, "float64"),
            Type::Char(_) => write!(self.writer, "char"),
            Type::Bool(_) => write!(self.writer, "bool"),
            Type::String(_) => write!(self.writer, "string"),
            Type::Tuple(types, _) => {
                write!(self.writer, "tuple<")?;
                for (i, ty) in types.iter().enumerate() {
                    if i > 0 {
                        write!(self.writer, ", ")?;
                    }

                    self.ty(ty)?;
                }

                write!(self.writer, ">")
            }
            Type::List(ty, _) => {
                write!(self.writer, "list<")?;
                self.ty(ty)?;
                write!(self.writer, ">")
            }
            Type::Option(ty, _) => {
                write!(self.writer, "option<")?;
                self.ty(ty)?;
                write!(self.writer, ">")
            }
            Type::Result { ok, err, .. } => match (ok, err) {
                (None, None) => write!(self.writer, "result"),
                (None, Some(err)) => {
                    write!(self.writer, "result<_, ")?;
                    self.ty(err)?;
                    write!(self.writer, ">")
                }
                (Some(ok), None) => {
                    write!(self.writer, "result<")?;
                    self.ty(ok)?;
                    write!(self.writer, ">")
                }
                (Some(ok), Some(err)) => {
                    write!(self.writer, "result<")?;
                    self.ty(ok)?;
                    write!(self.writer, ", ")?;
                    self.ty(err)?;
                    write!(self.writer, ">")
                }
            },
            Type::Borrow(id, _) => {
                write!(self.writer, "borrow<{id}>", id = self.source(id.span))
            }
            Type::Ident(id) => write!(self.writer, "{id}", id = self.source(id.span)),
        }
    }

    /// Prints the given inline interface.
    pub fn inline_interface(&mut self, iface: &InlineInterface) -> std::fmt::Result {
        write!(self.writer, "interface {{")?;
        self.newline()?;

        self.inc();
        for (i, item) in iface.items.iter().enumerate() {
            if i > 0 {
                self.newline()?;
            }

            self.interface_item(item)?;
            self.newline()?;
        }

        self.dec();
        self.indent()?;
        write!(self.writer, "}}")
    }

    /// Prints the given interface export.
    pub fn interface_item(&mut self, item: &InterfaceItem) -> std::fmt::Result {
        match item {
            InterfaceItem::Use(u) => self.use_type(u),
            InterfaceItem::Type(t) => self.item_type_decl(t),
            InterfaceItem::Export(e) => self.interface_export(e),
        }
    }

    /// Prints the given use type.
    pub fn use_type(&mut self, use_ty: &Use) -> std::fmt::Result {
        self.docs(&use_ty.docs)?;
        self.indent()?;
        write!(self.writer, "use ")?;
        self.use_path(&use_ty.path)?;

        write!(self.writer, ".{{ ")?;

        for (i, item) in use_ty.items.iter().enumerate() {
            if i > 0 {
                write!(self.writer, ", ")?;
            }

            write!(self.writer, "{id}", id = self.source(item.id.span))?;
            if let Some(as_id) = &item.as_id {
                write!(self.writer, " as {as_id}", as_id = self.source(as_id.span))?;
            }
        }

        write!(self.writer, " }};")
    }

    /// Prints the given use path.
    pub fn use_path(&mut self, path: &UsePath) -> std::fmt::Result {
        match path {
            UsePath::Package(p) => self.package_path(p),
            UsePath::Ident(id) => write!(self.writer, "{id}", id = self.source(id.span)),
        }
    }

    /// Prints the given type declaration.
    pub fn item_type_decl(&mut self, decl: &ItemTypeDecl) -> std::fmt::Result {
        match decl {
            ItemTypeDecl::Resource(r) => self.resource_decl(r),
            ItemTypeDecl::Variant(v) => self.variant_decl(v),
            ItemTypeDecl::Record(r) => self.record_decl(r),
            ItemTypeDecl::Flags(f) => self.flags_decl(f),
            ItemTypeDecl::Enum(e) => self.enum_decl(e),
            ItemTypeDecl::Alias(a) => self.type_alias(a),
        }
    }

    /// Prints the given resource declaration.
    pub fn resource_decl(&mut self, decl: &ResourceDecl) -> std::fmt::Result {
        self.docs(&decl.docs)?;
        self.indent()?;
        write!(
            self.writer,
            "resource {id} {{",
            id = self.source(decl.id.span)
        )?;
        self.newline()?;

        self.inc();
        for (i, method) in decl.methods.iter().enumerate() {
            if i > 0 {
                self.newline()?;
            }

            self.resource_method(method)?;
            self.newline()?;
        }

        self.dec();
        self.indent()?;
        write!(self.writer, "}}")
    }

    /// Prints the given resource method.
    pub fn resource_method(&mut self, method: &ResourceMethod) -> std::fmt::Result {
        match method {
            ResourceMethod::Constructor(c) => self.constructor(c),
            ResourceMethod::Method(m) => self.method(m),
        }
    }

    /// Prints the given constructor.
    pub fn constructor(&mut self, constructor: &Constructor) -> std::fmt::Result {
        self.docs(&constructor.docs)?;
        self.indent()?;
        write!(self.writer, "constructor(")?;
        self.named_types(&constructor.params)?;
        write!(self.writer, ");")
    }

    /// Prints the given method.
    pub fn method(&mut self, method: &Method) -> std::fmt::Result {
        self.docs(&method.docs)?;
        self.indent()?;
        write!(self.writer, "{id}: ", id = self.source(method.id.span))?;

        if method.is_static {
            write!(self.writer, "static ")?;
        }

        self.func_type(&method.ty)?;
        write!(self.writer, ";")
    }

    /// Prints the given function type reference.
    pub fn func_type_ref(&mut self, ty: &FuncTypeRef) -> std::fmt::Result {
        match ty {
            FuncTypeRef::Func(ty) => self.func_type(ty),
            FuncTypeRef::Ident(id) => write!(self.writer, "{id}", id = self.source(id.span)),
        }
    }

    /// Prints the given variant declaration.
    pub fn variant_decl(&mut self, decl: &VariantDecl) -> std::fmt::Result {
        self.docs(&decl.docs)?;
        self.indent()?;
        write!(
            self.writer,
            "variant {id} {{",
            id = self.source(decl.id.span)
        )?;
        self.newline()?;

        self.inc();
        for case in &decl.cases {
            self.indent()?;
            self.variant_case(case)?;
            write!(self.writer, ",")?;
            self.newline()?;
        }

        self.dec();
        self.indent()?;
        write!(self.writer, "}}")
    }

    /// Prints the given variant case.
    pub fn variant_case(&mut self, case: &VariantCase) -> std::fmt::Result {
        self.docs(&case.docs)?;
        self.indent()?;
        write!(self.writer, "{id}", id = self.source(case.id.span))?;

        if let Some(ty) = &case.ty {
            write!(self.writer, "(")?;
            self.ty(ty)?;
            write!(self.writer, ")")?;
        }

        Ok(())
    }

    /// Prints the given record declaration.
    pub fn record_decl(&mut self, decl: &RecordDecl) -> std::fmt::Result {
        self.docs(&decl.docs)?;
        self.indent()?;
        write!(
            self.writer,
            "record {id} {{",
            id = self.source(decl.id.span)
        )?;
        self.newline()?;

        self.inc();
        for field in &decl.fields {
            self.docs(&field.docs)?;
            self.indent()?;
            write!(self.writer, "{id}: ", id = self.source(field.id.span))?;
            self.ty(&field.ty)?;
            write!(self.writer, ",")?;
            self.newline()?;
        }

        self.dec();
        self.indent()?;
        write!(self.writer, "}}")
    }

    /// Prints the given flags declaration.
    pub fn flags_decl(&mut self, decl: &FlagsDecl) -> std::fmt::Result {
        self.docs(&decl.docs)?;
        self.indent()?;
        write!(self.writer, "flags {id} {{", id = self.source(decl.id.span))?;
        self.newline()?;

        self.inc();
        for flag in &decl.flags {
            self.docs(&flag.docs)?;
            self.indent()?;
            write!(self.writer, "{id},", id = self.source(flag.id.span))?;
            self.newline()?;
        }

        self.dec();
        self.indent()?;
        write!(self.writer, "}}")
    }

    /// Prints the given enum declaration.
    pub fn enum_decl(&mut self, decl: &EnumDecl) -> std::fmt::Result {
        self.docs(&decl.docs)?;
        self.indent()?;
        write!(self.writer, "enum {id} {{", id = self.source(decl.id.span))?;
        self.newline()?;

        self.inc();
        for case in &decl.cases {
            self.docs(&case.docs)?;
            self.indent()?;
            write!(self.writer, "{id},", id = self.source(case.id.span))?;
            self.newline()?;
        }

        self.dec();
        self.indent()?;
        write!(self.writer, "}}")
    }

    /// Prints the given type alias.
    pub fn type_alias(&mut self, alias: &TypeAlias) -> std::fmt::Result {
        self.docs(&alias.docs)?;
        self.indent()?;
        write!(self.writer, "type {id} = ", id = self.source(alias.id.span))?;
        match &alias.kind {
            TypeAliasKind::Func(ty) => self.func_type(ty)?,
            TypeAliasKind::Type(ty) => self.ty(ty)?,
        }

        write!(self.writer, ";")
    }

    /// Prints the given interface export.
    pub fn interface_export(&mut self, export: &InterfaceExport) -> std::fmt::Result {
        self.docs(&export.docs)?;
        self.indent()?;
        write!(self.writer, "{id}: ", id = self.source(export.id.span))?;
        self.func_type_ref(&export.ty)?;
        write!(self.writer, ";")
    }

    /// Prints the given type statement.
    pub fn type_statement(&mut self, stmt: &TypeStatement) -> std::fmt::Result {
        match stmt {
            TypeStatement::Interface(i) => self.interface_decl(i),
            TypeStatement::World(w) => self.world_decl(w),
            TypeStatement::Type(t) => self.type_decl(t),
        }
    }

    /// Prints the given interface declaration.
    pub fn interface_decl(&mut self, decl: &InterfaceDecl) -> std::fmt::Result {
        self.docs(&decl.docs)?;
        self.indent()?;
        write!(
            self.writer,
            "interface {id} {{",
            id = self.source(decl.id.span)
        )?;
        self.newline()?;

        self.inc();
        for (i, item) in decl.items.iter().enumerate() {
            if i > 0 {
                self.newline()?;
            }

            self.interface_item(item)?;
            self.newline()?;
        }

        self.dec();
        self.indent()?;
        write!(self.writer, "}}")
    }

    /// Prints the given world declaration.
    pub fn world_decl(&mut self, decl: &WorldDecl) -> std::fmt::Result {
        self.docs(&decl.docs)?;
        self.indent()?;
        write!(self.writer, "world {id} {{", id = self.source(decl.id.span))?;
        self.newline()?;

        self.inc();
        for (i, item) in decl.items.iter().enumerate() {
            if i > 0 {
                self.newline()?;
            }

            self.world_item(item)?;
            self.newline()?;
        }

        self.dec();
        self.indent()?;
        write!(self.writer, "}}")
    }

    /// Prints the given world item.
    pub fn world_item(&mut self, item: &WorldItem) -> std::fmt::Result {
        match item {
            WorldItem::Use(u) => self.use_type(u),
            WorldItem::Type(t) => self.item_type_decl(t),
            WorldItem::Import(i) => self.world_import(i),
            WorldItem::Export(e) => self.world_export(e),
            WorldItem::Include(i) => self.world_include(i),
        }
    }

    /// Prints the given world import.
    pub fn world_import(&mut self, import: &WorldImport) -> std::fmt::Result {
        self.docs(&import.docs)?;
        self.indent()?;
        write!(self.writer, "import ")?;

        self.world_item_path(&import.path)?;
        write!(self.writer, ";")
    }

    /// Prints the given world export.
    pub fn world_export(&mut self, export: &WorldExport) -> std::fmt::Result {
        self.docs(&export.docs)?;
        self.indent()?;
        write!(self.writer, "export ")?;

        self.world_item_path(&export.path)?;
        write!(self.writer, ";")
    }

    /// Prints the given world item path.
    pub fn world_item_path(&mut self, path: &WorldItemPath) -> std::fmt::Result {
        match path {
            WorldItemPath::Named(n) => self.named_world_item(n),
            WorldItemPath::Package(p) => self.package_path(p),
            WorldItemPath::Ident(id) => write!(self.writer, "{id}", id = self.source(id.span)),
        }
    }

    /// Prints the given named world item.
    pub fn named_world_item(&mut self, item: &NamedWorldItem) -> std::fmt::Result {
        write!(self.writer, "{id}: ", id = self.source(item.id.span))?;
        self.extern_type(&item.ty)
    }

    /// Prints the given extern type.
    pub fn extern_type(&mut self, ty: &ExternType) -> std::fmt::Result {
        match ty {
            ExternType::Ident(id) => write!(self.writer, "{id}", id = self.source(id.span)),
            ExternType::Func(ty) => self.func_type(ty),
            ExternType::Interface(i) => self.inline_interface(i),
        }
    }

    /// Prints the given world include.
    pub fn world_include(&mut self, include: &WorldInclude) -> std::fmt::Result {
        self.docs(&include.docs)?;
        self.indent()?;
        write!(self.writer, "include ")?;
        self.world_ref(&include.world)?;

        if !include.with.is_empty() {
            write!(self.writer, " with {{")?;
            self.newline()?;
            self.inc();

            for item in &include.with {
                self.indent()?;
                write!(
                    self.writer,
                    "{source} as {target},",
                    source = self.source(item.from.span),
                    target = self.source(item.to.span)
                )?;
                self.newline()?;
            }

            self.dec();
            self.indent()?;
            write!(self.writer, "}}")?;
        }

        write!(self.writer, ";")
    }

    /// Prints the given world reference.
    pub fn world_ref(&mut self, reference: &WorldRef) -> std::fmt::Result {
        match reference {
            WorldRef::Ident(id) => write!(self.writer, "{id}", id = self.source(id.span)),
            WorldRef::Package(p) => self.package_path(p),
        }
    }

    /// Prints the given type declaration.
    pub fn type_decl(&mut self, decl: &TypeDecl) -> std::fmt::Result {
        match decl {
            TypeDecl::Variant(v) => self.variant_decl(v),
            TypeDecl::Record(r) => self.record_decl(r),
            TypeDecl::Flags(f) => self.flags_decl(f),
            TypeDecl::Enum(e) => self.enum_decl(e),
            TypeDecl::Alias(a) => self.type_alias(a),
        }
    }

    /// Prints the given let statement.
    pub fn let_statement(&mut self, stmt: &LetStatement) -> std::fmt::Result {
        self.docs(&stmt.docs)?;
        self.indent()?;
        write!(self.writer, "let {id} = ", id = self.source(stmt.id.span))?;
        match &stmt.rhs {
            LetStatementRhs::Expr(expr) => self.expr(&expr)?,
            LetStatementRhs::Transform(transform) => self.transform(&transform)?,
        }
        write!(self.writer, ";")
    }

    /// Prints the given expression.
    pub fn expr(&mut self, expr: &Expr) -> std::fmt::Result {
        self.primary_expr(&expr.primary)?;
        for postfix in &expr.postfix {
            self.postfix_expr(postfix)?;
        }

        Ok(())
    }

    /// Prints the given transform.
    pub fn transform(&mut self, transform: &Transform) -> std::fmt::Result {
        write!(
            self.writer,
            "transform<{transformer}> {component}",
            transformer = self.source(transform.transformer.span),
            component = self.source(transform.component.span),
        )?;
        // TODO: write value
        Ok(())
    }

    /// Prints the given primary expression.
    pub fn primary_expr(&mut self, expr: &PrimaryExpr) -> std::fmt::Result {
        match expr {
            PrimaryExpr::New(e) => self.new_expr(e),
            PrimaryExpr::Nested(e) => {
                write!(self.writer, "(")?;
                self.expr(&e.inner)?;
                write!(self.writer, ")")
            }
            PrimaryExpr::Ident(id) => write!(self.writer, "{id}", id = self.source(id.span)),
        }
    }

    /// Prints the given new expression.
    pub fn new_expr(&mut self, expr: &NewExpr) -> std::fmt::Result {
        write!(
            self.writer,
            "new {name} {{",
            name = self.source(expr.component.span())
        )?;

        if expr.arguments.is_empty() {
            write!(self.writer, "}}")?;
            return Ok(());
        }

        if expr.arguments.len() == 1 {
            if let InstantiationArgument::Fill(_) = expr.arguments[0] {
                write!(self.writer, " ... }}")?;
                return Ok(());
            }
        }

        self.newline()?;
        self.inc();

        for arg in &expr.arguments {
            self.indent()?;

            match arg {
                InstantiationArgument::Inferred(id) => {
                    write!(self.writer, "{id},", id = self.source(id.span))?
                }
                InstantiationArgument::Spread(id) => {
                    write!(self.writer, "...{id},", id = self.source(id.span))?
                }
                InstantiationArgument::Named(arg) => {
                    match &arg.name {
                        InstantiationArgumentName::Ident(id) => {
                            write!(self.writer, "{id}: ", id = self.source(id.span))?;
                        }
                        InstantiationArgumentName::String(s) => {
                            write!(self.writer, "{s}: ", s = self.source(s.span))?;
                        }
                    }
                    self.expr(&arg.expr)?;
                    write!(self.writer, ",")?;
                }
                InstantiationArgument::Fill(_) => write!(self.writer, "...")?,
            }

            self.newline()?;
        }

        self.dec();
        self.indent()?;
        write!(self.writer, "}}")
    }

    /// Prints the given postfix expression.
    pub fn postfix_expr(&mut self, expr: &PostfixExpr) -> std::fmt::Result {
        match expr {
            PostfixExpr::Access(a) => self.access_expr(a),
            PostfixExpr::NamedAccess(a) => self.named_access_expr(a),
        }
    }

    /// Prints the given access expression.
    pub fn access_expr(&mut self, expr: &AccessExpr) -> std::fmt::Result {
        write!(self.writer, ".{id}", id = self.source(expr.id.span))
    }

    /// Prints the given named access expression.
    pub fn named_access_expr(&mut self, expr: &NamedAccessExpr) -> std::fmt::Result {
        write!(
            self.writer,
            "[{name}]",
            name = self.source(expr.string.span)
        )
    }

    /// Prints the given export statement.
    pub fn export_statement(&mut self, stmt: &ExportStatement) -> std::fmt::Result {
        self.docs(&stmt.docs)?;
        self.indent()?;

        write!(self.writer, "export ")?;

        self.expr(&stmt.expr)?;

        match &stmt.options {
            ExportOptions::None => {}
            ExportOptions::Spread(_) => {
                write!(self.writer, "...")?;
            }
            ExportOptions::Rename(name) => {
                write!(self.writer, " as {name}", name = self.source(name.span()))?;
            }
        }

        write!(self.writer, ";")
    }

    fn newline(&mut self) -> std::fmt::Result {
        writeln!(self.writer)?;
        self.indented = false;
        Ok(())
    }

    fn indent(&mut self) -> std::fmt::Result {
        if !self.indented {
            for _ in 0..self.indent {
                write!(self.writer, "{space}", space = self.space)?;
            }

            self.indented = true;
        }

        Ok(())
    }

    fn inc(&mut self) {
        self.indent = self.indent.saturating_add(1);
    }

    fn dec(&mut self) {
        self.indent = self.indent.saturating_sub(1);
    }

    fn source(&self, span: SourceSpan) -> &'a str {
        &self.source[span.offset()..span.offset() + span.len()]
    }
}
