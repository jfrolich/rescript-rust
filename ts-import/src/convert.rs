//! TypeScript types to ReScript declarations.
//!
//! The input is the checker's resolved `Type` values, not syntax: aliases are
//! already expanded, generics instantiated, conditional and mapped types
//! evaluated and return types inferred. A type is only resolved when this
//! module asks for it, so importing one function checks that function's
//! declaration and what its type mentions, nothing else.
//!
//! Where ReScript has no type for something, the converter picks the closest
//! sound type (usually `unknown`) and records a [`Note`] saying what was lost.

use std::collections::{HashMap, HashSet};

use tsrs_ast::{ModifierFlags, Symbol, SymbolFlags};
use tsrs_checker::{
    Checker, ElementFlags, LiteralValue, ObjectFlags, Signature, SignatureKind, Type, TypeFlags,
};
use tsrs_compiler::Program;
use tsrs_core::P;

use crate::model::{
    Ctor, Decl, DeclKind, External, Field, Item, Param, Payload, Tag, Ty, is_plain_field_name,
    lower_ident, shape_key, upper_ident,
};

/// What ReScript could not express exactly.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Gap {
    /// `any`: no ReScript type switches checking off.
    Any,
    /// `never` outside a function result.
    Never,
    /// More than one call signature; the first is used.
    Overloads,
    /// A constraint on a type parameter (`T extends U`).
    Constraint,
    /// A rest parameter in a function type that is not the imported function.
    RestInCallback,
    /// An explicit `this` parameter.
    ThisParameter,
    /// A union ReScript's untagged variants cannot tell apart at run time.
    Union,
    /// A constructor type (`new () => T`) or a class used as a value.
    Constructor,
    /// A function that also has properties.
    CallableObject,
    /// Properties together with an index signature.
    IndexSignature,
    /// A tuple with optional or rest elements, or a one-element tuple.
    Tuple,
    /// A type that still depends on a type parameter: conditional, mapped,
    /// indexed access or `keyof`.
    Deferred,
    /// `{}` or `object`.
    AnyObject,
    /// An intersection that is not an object type (a branded primitive).
    Intersection,
    /// An enum or namespace object used as a value.
    ValueObject,
    /// A type parameter that is not in scope where the type is declared.
    FreeTypeParameter,
    /// A generic function type nested in another type (a rank-2 type).
    GenericCallback,
    /// A type that nests deeper than the converter follows.
    Depth,
}

impl Gap {
    pub fn id(self) -> &'static str {
        match self {
            Gap::Any => "any",
            Gap::Never => "never",
            Gap::Overloads => "overloads",
            Gap::Constraint => "constraint",
            Gap::RestInCallback => "rest-in-callback",
            Gap::ThisParameter => "this-parameter",
            Gap::Union => "union",
            Gap::Constructor => "constructor",
            Gap::CallableObject => "callable-object",
            Gap::IndexSignature => "index-signature",
            Gap::Tuple => "tuple",
            Gap::Deferred => "deferred",
            Gap::AnyObject => "any-object",
            Gap::Intersection => "intersection",
            Gap::ValueObject => "value-object",
            Gap::FreeTypeParameter => "free-type-parameter",
            Gap::GenericCallback => "generic-callback",
            Gap::Depth => "depth",
        }
    }
}

/// One place where the ReScript type says less than the TypeScript type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Note {
    pub gap: Gap,
    /// The import the type belongs to, as the ReScript file names it.
    pub subject: String,
    /// Where in that import's type: `parameter options, field retries`.
    pub path: String,
    /// The TypeScript type.
    pub ts: String,
    pub message: String,
}

#[derive(Clone, Debug)]
struct Named {
    /// The ReScript module path the declaration is in.
    scope: Vec<String>,
    name: String,
    params: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Polarity {
    /// A value JavaScript hands to ReScript.
    Out,
    /// A value ReScript hands to JavaScript.
    In,
}

impl Polarity {
    fn flip(self) -> Polarity {
        match self {
            Polarity::Out => Polarity::In,
            Polarity::In => Polarity::Out,
        }
    }
}

/// A type either stands on its own or needs a declaration.
enum Structure {
    Ty(Ty),
    Decl(DeclKind),
}

/// What can be rolled back when a generic alias turns out not to be
/// expressible with its parameters.
#[derive(Clone)]
struct State {
    by_symbol: HashMap<P<Symbol>, Named>,
    by_type: HashMap<P<Type>, Named>,
    by_shape: HashMap<String, Named>,
    used: HashSet<String>,
    pending: Vec<Decl>,
    notes: Vec<Note>,
}

pub(crate) struct Converter<'a> {
    pub c: &'a mut Checker,
    program: &'static Program,
    state: State,
    /// Generic aliases whose declared type could not be converted.
    opaque_aliases: HashSet<P<Symbol>>,
    /// The ReScript module path of the request being converted.
    scope: Vec<String>,
    subject: String,
    /// Names the next anonymous declaration, and locates notes.
    path: Vec<String>,
    type_params: Vec<(P<Type>, String)>,
    polarity: Polarity,
    /// Free type variables are only legal in an external's own type.
    free_vars: bool,
    free_var_count: usize,
    deferred_seen: bool,
    depth: usize,
    /// The declared type of the interface or class being declared: there it
    /// is the declaration's body, anywhere else a reference to it.
    declaring: Option<P<Type>>,
}

const MAX_DEPTH: usize = 48;

fn num_literal(value: f64) -> Option<String> {
    if value.fract() == 0.0 && value.abs() < 2_147_483_648.0 {
        Some(format!("{}", value as i64))
    } else {
        None
    }
}

fn capitalize(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        Some(first) => first.to_ascii_uppercase().to_string() + chars.as_str(),
        None => String::new(),
    }
}

impl<'a> Converter<'a> {
    pub(crate) fn new(c: &'a mut Checker, program: &'static Program) -> Converter<'a> {
        Converter {
            c,
            program,
            state: State {
                by_symbol: HashMap::new(),
                by_type: HashMap::new(),
                by_shape: HashMap::new(),
                used: HashSet::new(),
                pending: Vec::new(),
                notes: Vec::new(),
            },
            opaque_aliases: HashSet::new(),
            scope: Vec::new(),
            subject: String::new(),
            path: Vec::new(),
            type_params: Vec::new(),
            polarity: Polarity::Out,
            free_vars: false,
            free_var_count: 0,
            deferred_seen: false,
            depth: 0,
            declaring: None,
        }
    }

    // ----- requests -------------------------------------------------------

    pub(crate) fn begin_request(&mut self, scope: &[String]) {
        self.scope = scope.to_vec();
        self.state.pending.clear();
        self.state.notes.clear();
    }

    pub(crate) fn take_notes(&mut self) -> Vec<Note> {
        std::mem::take(&mut self.state.notes)
    }

    /// The type declarations made since `begin_request`, dependencies first,
    /// with mutually recursive ones grouped.
    pub(crate) fn take_types(&mut self) -> Vec<Item> {
        let decls = std::mem::take(&mut self.state.pending);
        order_decls(decls)
    }

    fn begin_subject(&mut self, subject: &str) {
        self.subject = subject.to_string();
        self.path.clear();
        self.type_params.clear();
        self.polarity = Polarity::Out;
        self.free_var_count = 0;
        self.depth = 0;
    }

    /// An `external` for an exported value.
    pub(crate) fn value(
        &mut self,
        module: &str,
        export: &str,
        local: &str,
        symbol: P<Symbol>,
    ) -> Result<Vec<Item>, String> {
        let flags = symbol.flags();
        if !flags.intersects(SymbolFlags::Value) {
            return Err(format!(
                "`{export}` is a type in \"{module}\", not a value. Import it with `type {} = %ts(\"{module}#{export}\")`.",
                lower_ident(export)
            ));
        }
        self.begin_subject(local);
        if flags.intersects(SymbolFlags::Class) {
            // A class imported as a value is its constructor.
            return Ok(vec![self.constructor(module, export, local, symbol, &[])]);
        }
        let ty = self.c.get_type_of_symbol(symbol);
        let ts = self.c.type_to_string_exported(ty);
        // `export const version = "1.2.3"` has the literal's type; what a
        // ReScript program wants from it is a string.
        let ty = if ty.flags().intersects(TypeFlags::Literal) {
            self.c.get_base_type_of_literal_type(ty)
        } else {
            ty
        };
        self.free_vars = true;
        self.path.push(local.to_string());
        let mut attrs = vec![format!("module({})", crate::model::string_literal(module))];
        let converted = match self.single_signature(ty) {
            Some(signature) => {
                let (converted, variadic) = self.signature(signature, true);
                if variadic {
                    attrs.push("variadic".to_string());
                }
                converted
            }
            None => self.convert(ty),
        };
        self.path.pop();
        self.free_vars = false;
        Ok(vec![Item::External(External {
            name: local.to_string(),
            attrs,
            ty: converted,
            js_name: export.to_string(),
            ts: Some(ts),
        })])
    }

    /// The call signature of a function value, when it is all the type is.
    fn single_signature(&mut self, ty: P<Type>) -> Option<P<Signature>> {
        if !ty.flags().intersects(TypeFlags::Object) {
            return None;
        }
        let signatures = self.c.get_signatures_of_type(ty, SignatureKind::Call);
        let first = *signatures.first()?;
        if !self.visible_properties(ty).is_empty() {
            self.note(Gap::CallableObject, ty, "the function's properties are not imported");
        }
        if signatures.len() > 1 {
            self.note(
                Gap::Overloads,
                ty,
                &format!("{} overloads; the first one is imported", signatures.len()),
            );
        }
        Some(first)
    }

    /// `@new external` for a class.
    fn constructor(
        &mut self,
        module: &str,
        export: &str,
        local: &str,
        symbol: P<Symbol>,
        scope_attrs: &[String],
    ) -> Item {
        let statics = self.c.get_type_of_symbol(symbol);
        let ts = self.c.type_to_string_exported(statics);
        let signatures = self.c.get_signatures_of_type(statics, SignatureKind::Construct);
        self.free_vars = true;
        self.path.push(local.to_string());
        let ty = match signatures.first() {
            Some(&signature) => {
                if signatures.len() > 1 {
                    self.note(
                        Gap::Overloads,
                        statics,
                        &format!("{} constructor overloads; the first one is imported", signatures.len()),
                    );
                }
                self.signature(signature, true).0
            }
            None => {
                let instance = self.c.get_declared_type_of_symbol(symbol);
                Ty::Fn(Vec::new(), Box::new(self.convert(instance)))
            }
        };
        self.path.pop();
        self.free_vars = false;
        let mut attrs = vec![format!("module({})", crate::model::string_literal(module))];
        attrs.extend(scope_attrs.iter().cloned());
        attrs.push("new".to_string());
        Item::External(External {
            name: local.to_string(),
            attrs,
            ty,
            js_name: export.to_string(),
            ts: Some(ts),
        })
    }

    /// A module for a class: `type t`, `make` and the static members.
    pub(crate) fn class_module(
        &mut self,
        module: &str,
        export: &str,
        local: &str,
        symbol: P<Symbol>,
    ) -> Item {
        self.begin_subject(local);
        let instance = self.c.get_declared_type_of_symbol(symbol);
        let instance_ty = self.convert(instance);
        let params = match &instance_ty {
            Ty::App(_, args) => args
                .iter()
                .filter_map(|arg| match arg {
                    Ty::Var(name) => Some(name.clone()),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        };
        let mut items = vec![Item::Types(vec![Decl {
            name: "t".to_string(),
            params,
            kind: DeclKind::Alias(instance_ty),
            ts: None,
        }])];
        let statics = self.c.get_type_of_symbol(symbol);
        if !self.c.get_signatures_of_type(statics, SignatureKind::Construct).is_empty() {
            items.push(self.constructor(module, export, "make", symbol, &[]));
        }
        let scope_attr = format!("scope({})", crate::model::string_literal(export));
        for property in self.visible_properties(statics) {
            let name = property.name();
            let local_name = lower_ident(name);
            self.begin_subject(&format!("{local}.{local_name}"));
            let ty = self.c.get_type_of_symbol(property);
            let ts = self.c.type_to_string_exported(ty);
            self.free_vars = true;
            self.path.push(local_name.clone());
            let mut attrs = vec![
                format!("module({})", crate::model::string_literal(module)),
                scope_attr.clone(),
            ];
            let converted = match self.single_signature(ty) {
                Some(signature) => {
                    let (converted, variadic) = self.signature(signature, true);
                    if variadic {
                        attrs.push("variadic".to_string());
                    }
                    converted
                }
                None => self.convert(ty),
            };
            self.path.pop();
            self.free_vars = false;
            items.push(Item::External(External {
                name: local_name,
                attrs,
                ty: converted,
                js_name: name.to_string(),
                ts: Some(ts),
            }));
        }
        Item::Module(local.to_string(), items)
    }

    /// Declares the type an exported interface, class, alias or enum stands
    /// for, under the name the ReScript file chose.
    pub(crate) fn named_type(
        &mut self,
        module: &str,
        export: &str,
        local: Option<&str>,
        symbol: P<Symbol>,
    ) -> Result<(), String> {
        if !symbol.flags().intersects(SymbolFlags::Type) {
            return Err(format!(
                "`{export}` is a value in \"{module}\", not a type. Import it with `let {{{export}}} = %ts(\"{module}\")`."
            ));
        }
        self.begin_subject(local.unwrap_or(export));
        let Some(existing) = self.state.by_symbol.get(&symbol).cloned() else {
            self.declare_symbol(symbol, local);
            return Ok(());
        };
        // Already declared by an earlier import. Under another name, the new
        // name is an alias of it.
        let Some(local) = local else { return Ok(()) };
        if existing.scope == self.scope && existing.name == local {
            return Ok(());
        }
        let params: Vec<String> = (0..existing.params).map(|index| format!("t{index}")).collect();
        let args = params.iter().map(|param| Ty::Var(param.clone())).collect();
        let target = Ty::App(self.reference(&existing), args);
        self.state.used.insert(local.to_string());
        self.state.pending.push(Decl {
            name: local.to_string(),
            params,
            kind: DeclKind::Alias(target),
            ts: None,
        });
        Ok(())
    }

    // ----- names ----------------------------------------------------------

    fn fresh_type_name(&mut self, base: &str) -> String {
        let base = lower_ident(base);
        let mut name = base.clone();
        let mut index = 2;
        while self.state.used.contains(&name) {
            name = format!("{base}{index}");
            index += 1;
        }
        self.state.used.insert(name.clone());
        name
    }

    /// How the current request refers to a declaration.
    fn reference(&self, named: &Named) -> String {
        let common = named
            .scope
            .iter()
            .zip(self.scope.iter())
            .take_while(|(left, right)| left == right)
            .count();
        if common == named.scope.len() {
            named.name.clone()
        } else {
            format!("{}.{}", named.scope[common..].join("."), named.name)
        }
    }

    fn context_name(&self) -> String {
        let mut name = String::new();
        for (index, part) in self.path.iter().enumerate() {
            let part = lower_ident(part);
            if index == 0 {
                name.push_str(&part);
            } else {
                name.push_str(&capitalize(&part));
            }
        }
        if name.is_empty() { "t".to_string() } else { name }
    }

    fn note(&mut self, gap: Gap, ty: P<Type>, message: &str) {
        let ts = self.c.type_to_string_exported(ty);
        self.note_text(gap, ts, message);
    }

    fn note_text(&mut self, gap: Gap, ts: String, message: &str) {
        if gap == Gap::Deferred {
            self.deferred_seen = true;
        }
        let path = self.path.iter().skip(1).cloned().collect::<Vec<_>>().join(", ");
        let note = Note {
            gap,
            subject: self.subject.clone(),
            path,
            ts,
            message: message.to_string(),
        };
        if !self.state.notes.contains(&note) {
            self.state.notes.push(note);
        }
    }

    /// Whether the symbol is declared by TypeScript's own `lib.*.d.ts` files.
    fn is_lib_symbol(&self, symbol: P<Symbol>) -> bool {
        // A global declared across several library files is a merged symbol
        // with no file of its own, so go by its first declaration.
        let Some(&declaration) = symbol.declarations().first() else { return false };
        match tsrs_ast::get_source_file_of_node(declaration) {
            Some(file) => self.program.is_source_file_default_library(file.path()),
            None => false,
        }
    }

    // ----- types ----------------------------------------------------------

    /// The ReScript type for `ty`, declaring whatever it needs.
    pub(crate) fn convert(&mut self, ty: P<Type>) -> Ty {
        if self.depth >= MAX_DEPTH {
            self.note(Gap::Depth, ty, "the type nests too deeply to follow");
            return Ty::unknown();
        }
        self.depth += 1;
        let result = self.convert_inner(ty);
        self.depth -= 1;
        result
    }

    fn convert_inner(&mut self, ty: P<Type>) -> Ty {
        if let Some(named) = self.aliased(ty) {
            return named;
        }
        if let Some(named) = self.state.by_type.get(&ty).cloned() {
            return Ty::App(self.reference(&named), Vec::new());
        }
        match self.structure(ty) {
            Structure::Ty(converted) => converted,
            Structure::Decl(kind) => self.declare_anonymous(ty, kind),
        }
    }

    /// Declares a record or variant for a type TypeScript did not name.
    fn declare_anonymous(&mut self, ty: P<Type>, kind: DeclKind) -> Ty {
        let probe = Decl { name: String::new(), params: Vec::new(), kind, ts: None };
        let key = shape_key(&probe);
        if let Some(named) = self.state.by_shape.get(&key).cloned() {
            self.state.by_type.insert(ty, named.clone());
            return Ty::App(self.reference(&named), Vec::new());
        }
        let name = self.fresh_type_name(&self.context_name());
        let named = Named { scope: self.scope.clone(), name: name.clone(), params: 0 };
        self.state.by_type.insert(ty, named.clone());
        self.state.by_shape.insert(key, named);
        self.state.pending.push(Decl { name: name.clone(), ..probe });
        Ty::App(name, Vec::new())
    }

    /// A type written through a type alias keeps the alias's name.
    fn aliased(&mut self, ty: P<Type>) -> Option<Ty> {
        let alias = ty.alias()?;
        let symbol = alias.symbol()?;
        if self.is_lib_symbol(symbol) || self.opaque_aliases.contains(&symbol) {
            return None;
        }
        let args = alias.type_arguments();
        if let Some(named) = self.state.by_symbol.get(&symbol).cloned() {
            if named.params != args.len() {
                return None;
            }
            let args = self.convert_args(args);
            return Some(Ty::App(self.reference(&named), args));
        }
        if !self.declare_symbol(symbol, None) {
            return None;
        }
        let named = self.state.by_symbol.get(&symbol).cloned()?;
        if named.params != args.len() {
            return None;
        }
        let args = self.convert_args(args);
        Some(Ty::App(self.reference(&named), args))
    }

    fn convert_args(&mut self, args: &[P<Type>]) -> Vec<Ty> {
        let context = self.context_name();
        let saved = std::mem::replace(&mut self.path, vec![context]);
        let converted = args.iter().map(|&arg| self.convert(arg)).collect();
        self.path = saved;
        converted
    }

    /// Declares the type of an interface, class, enum or alias symbol.
    /// Returns false when a generic alias cannot be written with its
    /// parameters, in which case each use is converted on its own.
    fn declare_symbol(&mut self, symbol: P<Symbol>, local: Option<&str>) -> bool {
        let params = self.c.get_local_type_parameters_of_class_or_interface_or_type_alias_exported(symbol);
        let is_alias = symbol.flags().intersects(SymbolFlags::TypeAlias)
            && !symbol.flags().intersects(SymbolFlags::Class | SymbolFlags::Interface | SymbolFlags::Enum);
        let snapshot = if is_alias && !params.is_empty() { Some(self.state.clone()) } else { None };

        let name = match local {
            Some(local) => {
                self.state.used.insert(local.to_string());
                local.to_string()
            }
            None => self.fresh_type_name(symbol.name()),
        };
        let mut param_names: Vec<String> = Vec::new();
        for &param in &params {
            let base = param.symbol().map_or("t", |symbol| symbol.name());
            let mut param_name = lower_ident(base);
            let mut index = 2;
            while param_names.contains(&param_name) {
                param_name = format!("{}{index}", lower_ident(base));
                index += 1;
            }
            param_names.push(param_name);
        }
        self.state.by_symbol.insert(
            symbol,
            Named { scope: self.scope.clone(), name: name.clone(), params: params.len() },
        );

        // A declaration stands on its own: it sees its own parameters only.
        let saved_params = std::mem::replace(
            &mut self.type_params,
            params.iter().copied().zip(param_names.iter().cloned()).collect(),
        );
        let saved_path = std::mem::replace(&mut self.path, vec![name.clone()]);
        let saved_subject = std::mem::replace(&mut self.subject, name.clone());
        let saved_polarity = std::mem::replace(&mut self.polarity, Polarity::Out);
        let saved_free = std::mem::replace(&mut self.free_vars, false);
        let saved_deferred = std::mem::replace(&mut self.deferred_seen, false);

        let declared = self.c.get_declared_type_of_symbol(symbol);
        let saved_declaring = std::mem::replace(&mut self.declaring, Some(declared));
        let kind = if symbol.flags().intersects(SymbolFlags::Enum) {
            self.enum_decl(symbol)
        } else {
            match self.structure(declared) {
                Structure::Ty(ty) => DeclKind::Alias(ty),
                Structure::Decl(kind) => kind,
            }
        };
        let deferred = self.deferred_seen;

        self.declaring = saved_declaring;
        self.type_params = saved_params;
        self.path = saved_path;
        self.subject = saved_subject;
        self.polarity = saved_polarity;
        self.free_vars = saved_free;
        self.deferred_seen = saved_deferred;

        if let Some(snapshot) = snapshot
            && deferred
        {
            self.state = snapshot;
            self.opaque_aliases.insert(symbol);
            return false;
        }
        self.state.pending.push(Decl { name, params: param_names, kind, ts: None });
        true
    }

    fn enum_decl(&mut self, symbol: P<Symbol>) -> DeclKind {
        let mut ctors = Vec::new();
        let Some(exports) = symbol.exports() else {
            return DeclKind::Alias(Ty::name("float"));
        };
        let mut members: Vec<P<Symbol>> = exports
            .values()
            .into_iter()
            .filter(|member| member.flags().intersects(SymbolFlags::EnumMember))
            .collect();
        members.sort_by_key(|member| member.declarations().first().map(|node| node.pos()));
        for member in members {
            let ty = self.c.get_declared_type_of_symbol(member);
            let tag = match literal_tag(ty) {
                Some(tag) => tag,
                // A computed member: the enum is just a number.
                None => return DeclKind::Alias(Ty::name("float")),
            };
            ctors.push(Ctor { name: upper_ident(member.name()), tag: Some(tag), payload: Payload::None });
        }
        if ctors.is_empty() {
            return DeclKind::Alias(Ty::name("float"));
        }
        DeclKind::Variant { tag: None, ctors }
    }

    fn any_like(&mut self, ty: P<Type>, is_any: bool) -> Ty {
        if is_any {
            self.note(
                Gap::Any,
                ty,
                "`any` turns checking off; it is imported as `unknown` (or a type variable for an argument)",
            );
        }
        if self.free_vars && self.polarity == Polarity::In {
            return self.fresh_var();
        }
        Ty::unknown()
    }

    fn fresh_var(&mut self) -> Ty {
        loop {
            let index = self.free_var_count;
            self.free_var_count += 1;
            let name = if index < 26 {
                ((b'a' + index as u8) as char).to_string()
            } else {
                format!("a{index}")
            };
            if !self.type_params.iter().any(|(_, used)| *used == name) {
                return Ty::Var(name);
            }
        }
    }

    fn structure(&mut self, ty: P<Type>) -> Structure {
        let flags = ty.flags();
        let simple = |name: &str| Structure::Ty(Ty::name(name));
        if flags.intersects(TypeFlags::Any) {
            return Structure::Ty(self.any_like(ty, true));
        }
        if flags.intersects(TypeFlags::Unknown) {
            return Structure::Ty(self.any_like(ty, false));
        }
        if flags.intersects(TypeFlags::Never) {
            if self.free_vars && self.polarity == Polarity::Out {
                return Structure::Ty(self.fresh_var());
            }
            self.note(Gap::Never, ty, "ReScript has no empty type");
            return Structure::Ty(Ty::unknown());
        }
        if flags.intersects(TypeFlags::Union) {
            if flags.intersects(TypeFlags::Boolean) {
                return simple("bool");
            }
            if flags.intersects(TypeFlags::EnumLiteral)
                && let Some(symbol) = ty.symbol()
                && symbol.flags().intersects(SymbolFlags::Enum)
            {
                return Structure::Ty(self.symbol_type(symbol, &[]));
            }
            return self.union(ty);
        }
        if flags.intersects(TypeFlags::EnumLiteral)
            && let Some(parent) = ty.symbol().and_then(|symbol| symbol.parent())
            && parent.flags().intersects(SymbolFlags::Enum)
        {
            // One member of an enum: the enum's type is the closest.
            return Structure::Ty(self.symbol_type(parent, &[]));
        }
        if flags.intersects(TypeFlags::StringLiteral | TypeFlags::NumberLiteral) {
            return match literal_tag(ty) {
                Some(tag) if poly_tag_ok(&tag) => Structure::Ty(Ty::Poly(vec![tag])),
                _ if flags.intersects(TypeFlags::StringLiteral) => simple("string"),
                _ => simple("float"),
            };
        }
        if flags.intersects(TypeFlags::String | TypeFlags::TemplateLiteral | TypeFlags::StringMapping) {
            return simple("string");
        }
        if flags.intersects(TypeFlags::Number | TypeFlags::Enum) {
            return simple("float");
        }
        if flags.intersects(TypeFlags::Boolean | TypeFlags::BooleanLiteral) {
            return simple("bool");
        }
        if flags.intersects(TypeFlags::BigInt | TypeFlags::BigIntLiteral) {
            return simple("bigint");
        }
        if flags.intersects(TypeFlags::ESSymbol | TypeFlags::UniqueESSymbol) {
            return simple("Symbol.t");
        }
        if flags.intersects(TypeFlags::Void | TypeFlags::Undefined) {
            return simple("unit");
        }
        if flags.intersects(TypeFlags::Null) {
            return Structure::Ty(Ty::app("Null.t", vec![Ty::unknown()]));
        }
        if flags.intersects(TypeFlags::TypeParameter) {
            if let Some((_, name)) = self.type_params.iter().rev().find(|(param, _)| *param == ty) {
                return Structure::Ty(Ty::Var(name.clone()));
            }
            // `this` as a type is the class or interface it appears in.
            if ty.as_type_parameter().is_this_type()
                && let Some(constraint) = self.c.get_base_constraint_of_type(ty)
                && constraint != ty
            {
                return Structure::Ty(self.convert(constraint));
            }
            if let Some(constraint) = self.c.get_base_constraint_of_type(ty)
                && constraint != ty
                && !constraint.flags().intersects(TypeFlags::AnyOrUnknown)
            {
                self.note(Gap::FreeTypeParameter, ty, "the type parameter is not in scope here; its constraint is used");
                return Structure::Ty(self.convert(constraint));
            }
            self.note(Gap::FreeTypeParameter, ty, "the type parameter is not in scope here");
            return Structure::Ty(Ty::unknown());
        }
        if flags.intersects(TypeFlags::Intersection) {
            return self.intersection(ty);
        }
        if flags.intersects(TypeFlags::Object) {
            return self.object(ty);
        }
        if flags.intersects(TypeFlags::NonPrimitive) {
            self.note(Gap::AnyObject, ty, "`object` says nothing about the value's fields");
            return Structure::Ty(Ty::unknown());
        }
        // keyof T, T[K], conditional types and substitutions that still
        // depend on a type parameter.
        if flags.intersects(TypeFlags::Index) {
            self.note(Gap::Deferred, ty, "`keyof` of a type parameter; any string is accepted");
            return simple("string");
        }
        if let Some(constraint) = self.c.get_base_constraint_of_type(ty)
            && constraint != ty
            && !constraint.flags().intersects(TypeFlags::AnyOrUnknown)
        {
            self.note(Gap::Deferred, ty, "the type depends on a type parameter; its constraint is used");
            return Structure::Ty(self.convert(constraint));
        }
        self.note(Gap::Deferred, ty, "the type depends on a type parameter");
        Structure::Ty(Ty::unknown())
    }

    /// The declared type of a class, interface or enum, applied to `args`.
    fn symbol_type(&mut self, symbol: P<Symbol>, args: &[P<Type>]) -> Ty {
        if self.is_lib_symbol(symbol) {
            return self.lib_type(symbol, args);
        }
        if !self.state.by_symbol.contains_key(&symbol) {
            self.declare_symbol(symbol, None);
        }
        let Some(named) = self.state.by_symbol.get(&symbol).cloned() else {
            return Ty::unknown();
        };
        let args: Vec<P<Type>> = args.iter().copied().take(named.params).collect();
        if args.len() != named.params {
            return Ty::App(self.reference(&named), vec![Ty::unknown(); named.params]);
        }
        let args = self.convert_args(&args);
        Ty::App(self.reference(&named), args)
    }

    /// A type declared in TypeScript's own library files.
    fn lib_type(&mut self, symbol: P<Symbol>, args: &[P<Type>]) -> Ty {
        let name = symbol.name();
        let arg = |this: &mut Self, index: usize| match args.get(index) {
            Some(&arg) => this.convert(arg),
            None => Ty::unknown(),
        };
        match name {
            "Promise" | "PromiseLike" => Ty::app("promise", vec![arg(self, 0)]),
            "Array" | "ReadonlyArray" => Ty::app("array", vec![arg(self, 0)]),
            "Map" | "ReadonlyMap" => Ty::app("Map.t", vec![arg(self, 0), arg(self, 1)]),
            "Set" | "ReadonlySet" => Ty::app("Set.t", vec![arg(self, 0)]),
            "WeakMap" => Ty::app("WeakMap.t", vec![arg(self, 0), arg(self, 1)]),
            "WeakSet" => Ty::app("WeakSet.t", vec![arg(self, 0)]),
            "Iterator" | "Iterable" | "IterableIterator" | "IteratorObject" | "Generator"
            | "ArrayIterator" | "MapIterator" | "SetIterator" => {
                Ty::app("Iterator.t", vec![arg(self, 0)])
            }
            "AsyncIterator" | "AsyncIterable" | "AsyncIterableIterator" | "AsyncGenerator"
            | "AsyncIteratorObject" => Ty::app("AsyncIterator.t", vec![arg(self, 0)]),
            "Date" => Ty::name("Date.t"),
            "RegExp" => Ty::name("RegExp.t"),
            "Error" | "TypeError" | "RangeError" | "SyntaxError" | "ReferenceError" | "EvalError"
            | "URIError" | "AggregateError" => Ty::name("JsError.t"),
            "ArrayBuffer" | "SharedArrayBuffer" => Ty::name("ArrayBuffer.t"),
            "DataView" => Ty::name("DataView.t"),
            "Int8Array" | "Uint8Array" | "Uint8ClampedArray" | "Int16Array" | "Uint16Array"
            | "Int32Array" | "Uint32Array" | "Float32Array" | "Float64Array" | "BigInt64Array"
            | "BigUint64Array" => Ty::name(&format!("{name}.t")),
            "String" => Ty::name("string"),
            "Number" => Ty::name("float"),
            "Boolean" => Ty::name("bool"),
            "Symbol" => Ty::name("Symbol.t"),
            "BigInt" => Ty::name("bigint"),
            _ => {
                // Any other library type (the DOM, Intl, ...) is opaque: it can
                // be passed around, and a binding can be written for what is
                // needed from it.
                if let Some(named) = self.state.by_symbol.get(&symbol).cloned() {
                    return Ty::App(self.reference(&named), Vec::new());
                }
                let type_name = self.fresh_type_name(name);
                let named = Named { scope: self.scope.clone(), name: type_name.clone(), params: 0 };
                self.state.by_symbol.insert(symbol, named);
                self.state.pending.push(Decl {
                    name: type_name.clone(),
                    params: Vec::new(),
                    kind: DeclKind::Abstract,
                    ts: Some(name.to_string()),
                });
                Ty::App(type_name, Vec::new())
            }
        }
    }

    fn object(&mut self, ty: P<Type>) -> Structure {
        let object_flags = ty.object_flags();
        // The declared type of a generic interface, or of any class, is a
        // reference to itself, so this comes before the reference case.
        if self.declaring == Some(ty) {
            self.declaring = None;
            return self.anonymous_object(ty);
        }
        if object_flags.intersects(ObjectFlags::Reference) {
            let args = self.c.get_type_arguments(ty);
            if self.c.is_array_type(ty) {
                let element = match args.first() {
                    Some(&element) => self.convert(element),
                    None => Ty::unknown(),
                };
                return Structure::Ty(Ty::app("array", vec![element]));
            }
            if let Some(target) = ty.target()
                && target.object_flags().intersects(ObjectFlags::Tuple)
            {
                return Structure::Ty(self.tuple(ty, target, args));
            }
            if let Some(symbol) = ty.symbol() {
                return Structure::Ty(self.symbol_type(symbol, args));
            }
        }
        if object_flags.intersects(ObjectFlags::ClassOrInterface)
            && let Some(symbol) = ty.symbol()
        {
            if self.is_lib_symbol(symbol) {
                return Structure::Ty(self.lib_type(symbol, &[]));
            }
            let params: Vec<P<Type>> =
                self.c.get_local_type_parameters_of_class_or_interface_or_type_alias_exported(symbol);
            return Structure::Ty(self.symbol_type(symbol, &params));
        }
        self.anonymous_object(ty)
    }

    /// The properties a ReScript record can have: public, named by a string.
    fn visible_properties(&mut self, ty: P<Type>) -> Vec<P<Symbol>> {
        self.c
            .get_properties_of_type(ty)
            .iter()
            .copied()
            .filter(|property| {
                let name = property.name();
                if name.starts_with("__@") || name.starts_with('#') || name == "prototype" {
                    return false;
                }
                if property.flags().intersects(SymbolFlags::Prototype) {
                    return false;
                }
                if property.declarations().is_empty() {
                    return true;
                }
                let modifiers = tsrs_checker::get_declaration_modifier_flags_from_symbol_exported(*property);
                !modifiers.intersects(ModifierFlags::Private | ModifierFlags::Protected)
            })
            .collect()
    }

    fn anonymous_object(&mut self, ty: P<Type>) -> Structure {
        let calls = self.c.get_signatures_of_type(ty, SignatureKind::Call);
        let constructs = self.c.get_signatures_of_type(ty, SignatureKind::Construct);
        let properties = self.visible_properties(ty);
        let index_infos = self.c.get_index_infos_of_type(ty);

        if let Some(symbol) = ty.symbol() {
            let flags = symbol.flags();
            if !constructs.is_empty() {
                self.note(
                    Gap::Constructor,
                    ty,
                    "a constructor is not a ReScript value; import the class as a module instead",
                );
                return Structure::Ty(Ty::unknown());
            }
            if flags.intersects(SymbolFlags::Enum | SymbolFlags::ValueModule)
                && !flags.intersects(SymbolFlags::Function)
            {
                self.note(Gap::ValueObject, ty, "enum and namespace objects are not imported as values");
                return Structure::Ty(Ty::unknown());
            }
        } else if !constructs.is_empty() {
            self.note(Gap::Constructor, ty, "a constructor type has no ReScript counterpart");
            return Structure::Ty(Ty::unknown());
        }

        if let Some(&first) = calls.first() {
            if !properties.is_empty() {
                self.note(Gap::CallableObject, ty, "the function's properties are dropped");
            }
            if calls.len() > 1 {
                self.note(Gap::Overloads, ty, &format!("{} overloads; the first one is used", calls.len()));
            }
            // Outside an external's own type there is nothing to bind the
            // signature's type parameters to.
            let generic = self.free_vars;
            return Structure::Ty(self.signature_with(first, false, generic).0);
        }
        if properties.is_empty() {
            if let Some(info) = index_infos.first() {
                let saved = self.free_vars;
                self.free_vars = false;
                let value = self.convert(info.value_type());
                self.free_vars = saved;
                return Structure::Ty(Ty::app("dict", vec![value]));
            }
            self.note(Gap::AnyObject, ty, "`{}` accepts any value that is not null or undefined");
            return Structure::Ty(Ty::unknown());
        }
        if !index_infos.is_empty() {
            self.note(Gap::IndexSignature, ty, "the index signature is dropped; only the named properties are imported");
        }
        Structure::Decl(DeclKind::Record(self.fields(&properties, None)))
    }

    fn fields(&mut self, properties: &[P<Symbol>], skip: Option<&str>) -> Vec<Field> {
        let saved_free = std::mem::replace(&mut self.free_vars, false);
        let saved_polarity = std::mem::replace(&mut self.polarity, Polarity::Out);
        let mut fields: Vec<Field> = Vec::new();
        for &property in properties {
            let js_name = property.name();
            if skip == Some(js_name) {
                continue;
            }
            let mut name = if is_plain_field_name(js_name) { js_name.to_string() } else { lower_ident(js_name) };
            let mut index = 2;
            while fields.iter().any(|field| field.name == name) {
                name = format!("{}{index}", lower_ident(js_name));
                index += 1;
            }
            let ty = self.c.get_type_of_symbol(property);
            let optional = property.flags().intersects(SymbolFlags::Optional);
            self.path.push(js_name.to_string());
            // A generic method is a polymorphic field: `map: 'u. ('t => 'u) => box<'u>`.
            let generic_method = if optional || ty.alias().is_some() || !ty.flags().intersects(TypeFlags::Object) {
                None
            } else {
                match self.c.get_signatures_of_type(ty, SignatureKind::Call) {
                    [only] if !only.type_parameters().is_empty() && self.visible_properties(ty).is_empty() => Some(*only),
                    _ => None,
                }
            };
            let (converted, poly) = match generic_method {
                Some(signature) => {
                    let (converted, _, poly) = self.signature_with(signature, false, true);
                    (converted, poly)
                }
                None if optional => (self.convert_without_undefined(ty), Vec::new()),
                None => (self.convert(ty), Vec::new()),
            };
            self.path.pop();
            fields.push(Field {
                js_name: if name == js_name { None } else { Some(js_name.to_string()) },
                name,
                optional,
                poly,
                ty: converted,
            });
        }
        self.free_vars = saved_free;
        self.polarity = saved_polarity;
        fields
    }

    /// The type of an optional field or argument: `undefined` is what the
    /// `?` already says.
    fn convert_without_undefined(&mut self, ty: P<Type>) -> Ty {
        if !ty.flags().intersects(TypeFlags::Union) || ty.flags().intersects(TypeFlags::Boolean) {
            return self.convert(ty);
        }
        let (members, _, null) = split_nullish(ty);
        if members.len() == ty.types().len() {
            return self.convert(ty);
        }
        let inner = match self.union_members(ty, &members) {
            Structure::Ty(inner) => inner,
            Structure::Decl(kind) => self.declare_anonymous(ty, kind),
        };
        if null { Ty::app("Null.t", vec![inner]) } else { inner }
    }

    fn tuple(&mut self, ty: P<Type>, target: P<Type>, args: &[P<Type>]) -> Ty {
        let infos = target.as_tuple_type().element_infos();
        let fixed = infos.iter().all(|info| info.tuple_element_flags() == ElementFlags::Required);
        if !fixed || args.len() < infos.len() {
            self.note(Gap::Tuple, ty, "tuples with optional or rest elements are imported as arrays");
            return Ty::app("array", vec![Ty::unknown()]);
        }
        let elements: Vec<Ty> = args.iter().take(infos.len()).map(|&arg| self.convert(arg)).collect();
        match elements.len() {
            0 => Ty::app("array", vec![Ty::unknown()]),
            1 => {
                self.note(Gap::Tuple, ty, "ReScript has no one-element tuple; an array is used");
                Ty::app("array", elements)
            }
            _ => Ty::Tuple(elements),
        }
    }

    fn intersection(&mut self, ty: P<Type>) -> Structure {
        // A branded primitive (`string & {__brand: "Id"}`) is the primitive.
        let primitive = ty.types().iter().copied().find(|member| {
            member.flags().intersects(
                TypeFlags::String | TypeFlags::Number | TypeFlags::Boolean | TypeFlags::BigInt | TypeFlags::ESSymbol,
            )
        });
        if let Some(primitive) = primitive {
            self.note(Gap::Intersection, ty, "the brand is dropped; the primitive type is used");
            return self.structure(primitive);
        }
        let properties = self.visible_properties(ty);
        if properties.is_empty() {
            self.note(Gap::Intersection, ty, "the intersection has no properties to import");
            return Structure::Ty(Ty::unknown());
        }
        // TypeScript already merged the members: an intersection of object
        // types is one record with all the properties.
        Structure::Decl(DeclKind::Record(self.fields(&properties, None)))
    }

    fn union(&mut self, ty: P<Type>) -> Structure {
        let (members, undefined, null) = split_nullish(ty);
        let inner = self.union_members(ty, &members);
        if !undefined && !null {
            return inner;
        }
        // An untagged variant can hold `null` itself, as `JSON.t` does.
        let (inner, null) = match inner {
            Structure::Decl(DeclKind::Variant { tag: None, mut ctors }) if null => {
                let name = unique_ctor(&ctors, "Null");
                ctors.push(Ctor { name, tag: Some(Tag::Null), payload: Payload::None });
                (Structure::Decl(DeclKind::Variant { tag: None, ctors }), false)
            }
            inner => (inner, null),
        };
        if !undefined && !null {
            return inner;
        }
        let inner = match inner {
            Structure::Ty(inner) => inner,
            Structure::Decl(kind) => self.declare_anonymous(ty, kind),
        };
        Structure::Ty(match (undefined, null) {
            (true, true) => Ty::app("Nullable.t", vec![inner]),
            (false, true) => Ty::app("Null.t", vec![inner]),
            _ if inner.is_unit() => inner,
            _ => Ty::app("option", vec![inner]),
        })
    }

    /// The union of `members`, none of which is `null` or `undefined`.
    fn union_members(&mut self, whole: P<Type>, members: &[P<Type>]) -> Structure {
        match members {
            [] => return Structure::Ty(Ty::name("unit")),
            [one] => return Structure::Ty(self.convert(*one)),
            _ => {}
        }
        // `true | false` is `boolean`.
        let is_bool_literal = |member: &P<Type>| member.flags().intersects(TypeFlags::BooleanLiteral);
        let bool_literals = members.iter().filter(|member| is_bool_literal(member)).count();
        let mut members: Vec<P<Type>> = members.to_vec();
        let mut whole_boolean = false;
        if bool_literals == 2 {
            members.retain(|member| !is_bool_literal(member));
            whole_boolean = true;
            if members.is_empty() {
                return Structure::Ty(Ty::name("bool"));
            }
        }

        // Only literals: a polymorphic variant, which needs no declaration.
        if !whole_boolean {
            let tags: Vec<Tag> = members.iter().filter_map(|&member| literal_tag(member)).collect();
            if tags.len() == members.len() && tags.iter().all(poly_tag_ok) {
                return Structure::Ty(Ty::Poly(tags));
            }
            if let Some(tagged) = self.tagged_union(&members) {
                return Structure::Decl(tagged);
            }
        }
        match self.untagged_union(&members, whole_boolean) {
            Some(kind) => Structure::Decl(kind),
            None => {
                self.note(
                    Gap::Union,
                    whole,
                    "ReScript cannot tell the members of this union apart at run time",
                );
                Structure::Ty(Ty::unknown())
            }
        }
    }

    /// Object types that share a property holding a different literal in each
    /// member: a variant tagged by that property.
    fn tagged_union(&mut self, members: &[P<Type>]) -> Option<DeclKind> {
        let is_plain_object = |this: &mut Self, member: P<Type>| {
            member.flags().intersects(TypeFlags::Object)
                && !this.c.is_array_type(member)
                && this.c.get_signatures_of_type(member, SignatureKind::Call).is_empty()
        };
        if !members.iter().all(|&member| is_plain_object(self, member)) {
            return None;
        }
        let candidates = self.visible_properties(members[0]);
        for candidate in candidates {
            let name = candidate.name();
            let mut tags: Vec<Tag> = Vec::new();
            for &member in members {
                let Some(property) = self.c.get_property_of_type(member, name) else { break };
                if property.flags().intersects(SymbolFlags::Optional) {
                    break;
                }
                let property_type = self.c.get_type_of_symbol(property);
                let Some(tag) = literal_tag(property_type) else { break };
                if tags.contains(&tag) {
                    break;
                }
                tags.push(tag);
            }
            if tags.len() != members.len() {
                continue;
            }
            let mut ctors: Vec<Ctor> = Vec::new();
            for (&member, tag) in members.iter().zip(tags) {
                let base = match &tag {
                    Tag::Str(text) => upper_ident(text),
                    Tag::Num(text) => upper_ident(text),
                    Tag::Bool(value) => upper_ident(&value.to_string()),
                    Tag::Null => "Null".to_string(),
                    Tag::Undefined => "Undefined".to_string(),
                };
                let ctor_name = unique_ctor(&ctors, &base);
                let properties = self.visible_properties(member);
                self.path.push(ctor_name.clone());
                let fields = self.fields(&properties, Some(name));
                self.path.pop();
                ctors.push(Ctor {
                    name: ctor_name,
                    tag: Some(tag),
                    payload: if fields.is_empty() { Payload::None } else { Payload::Record(fields) },
                });
            }
            return Some(DeclKind::Variant { tag: Some(name.to_string()), ctors });
        }
        None
    }

    /// A union ReScript can discriminate with `typeof`, `Array.isArray` and
    /// `instanceof`: at most one member of each runtime kind.
    fn untagged_union(&mut self, members: &[P<Type>], whole_boolean: bool) -> Option<DeclKind> {
        let mut ctors: Vec<Ctor> = Vec::new();
        let mut kinds: HashSet<&'static str> = HashSet::new();
        if whole_boolean {
            kinds.insert("boolean");
            ctors.push(Ctor { name: "Boolean".to_string(), tag: None, payload: Payload::Ty(Ty::name("bool")) });
        }
        let saved_free = std::mem::replace(&mut self.free_vars, false);
        let mut ok = true;
        for &member in members {
            if let Some(tag) = literal_tag(member) {
                let base = match &tag {
                    Tag::Str(text) => upper_ident(text),
                    Tag::Num(text) => upper_ident(text),
                    Tag::Bool(value) => upper_ident(&value.to_string()),
                    Tag::Null => "Null".to_string(),
                    Tag::Undefined => "Undefined".to_string(),
                };
                let name = unique_ctor(&ctors, &base);
                ctors.push(Ctor { name, tag: Some(tag), payload: Payload::None });
                continue;
            }
            let flags = member.flags();
            let (kind, base): (&'static str, &str) = if flags.intersects(TypeFlags::String | TypeFlags::TemplateLiteral | TypeFlags::StringMapping) {
                ("string", "String")
            } else if flags.intersects(TypeFlags::Number) {
                ("number", "Number")
            } else if flags.intersects(TypeFlags::BigInt) {
                ("bigint", "BigInt")
            } else if flags.intersects(TypeFlags::Boolean) {
                ("boolean", "Boolean")
            } else if flags.intersects(TypeFlags::Object) {
                if self.c.is_array_or_tuple_type(member) {
                    ("array", "Array")
                } else if !self.c.get_signatures_of_type(member, SignatureKind::Call).is_empty() {
                    ("function", "Function")
                } else {
                    match member.symbol().filter(|symbol| self.is_lib_symbol(*symbol)).map(|symbol| symbol.name()) {
                        Some("Date") => ("date", "Date"),
                        Some("RegExp") => ("regexp", "RegExp"),
                        Some("Promise") => ("promise", "Promise"),
                        _ => ("object", "Object"),
                    }
                }
            } else {
                ok = false;
                break;
            };
            if !kinds.insert(kind) {
                ok = false;
                break;
            }
            self.path.push(base.to_string());
            let payload = self.convert(member);
            self.path.pop();
            // An object member is named after its type: `User(user)`.
            let base = match (&payload, kind) {
                (Ty::App(name, _), "object") if !name.contains('.') && name != "dict" => capitalize(name),
                _ => base.to_string(),
            };
            let name = unique_ctor(&ctors, &base);
            ctors.push(Ctor { name, tag: None, payload: Payload::Ty(payload) });
        }
        self.free_vars = saved_free;
        if ok { Some(DeclKind::Variant { tag: None, ctors }) } else { None }
    }

    /// A function type. `top` is the imported function itself, where a rest
    /// parameter becomes `@variadic`; the flag is the second result.
    fn signature(&mut self, signature: P<Signature>, top: bool) -> (Ty, bool) {
        let (ty, variadic, _) = self.signature_with(signature, top, true);
        (ty, variadic)
    }

    /// As [`Self::signature`]; the third result is the names of the
    /// signature's own type parameters. With `generic` false they are not
    /// type variables: a declaration cannot quantify over the type
    /// parameters of a function type nested inside it.
    fn signature_with(&mut self, signature: P<Signature>, top: bool, generic: bool) -> (Ty, bool, Vec<String>) {
        let saved_params = self.type_params.len();
        if !generic && !signature.type_parameters().is_empty() {
            self.note_text(
                Gap::GenericCallback,
                signature.type_parameters().iter().filter_map(|param| param.symbol()).map(|symbol| symbol.name()).collect::<Vec<_>>().join(", "),
                "a function type that is generic by itself can only be a record field; its type parameters are `unknown` here",
            );
        }
        for &param in signature.type_parameters() {
            if !generic {
                continue;
            }
            let base = param.symbol().map_or("t", |symbol| symbol.name());
            let mut name = lower_ident(base);
            let mut index = 2;
            while self.type_params.iter().any(|(_, used)| *used == name) {
                name = format!("{}{index}", lower_ident(base));
                index += 1;
            }
            if let Some(constraint) = self.c.get_constraint_of_type_parameter(param)
                && !constraint.flags().intersects(TypeFlags::AnyOrUnknown)
            {
                let ts = format!("{} extends {}", base, self.c.type_to_string_exported(constraint));
                self.note_text(Gap::Constraint, ts, "the constraint is not checked by ReScript");
            }
            self.type_params.push((param, name));
        }
        if signature.this_parameter().is_some() {
            self.note_text(Gap::ThisParameter, "this".to_string(), "the `this` parameter is dropped");
        }

        let parameters = signature.parameters();
        let required = signature.min_argument_count();
        let rest = signature.has_rest_parameter();
        let mut params: Vec<Param> = Vec::new();
        let mut variadic = false;
        let outer = self.polarity;
        self.polarity = outer.flip();
        for (index, &parameter) in parameters.iter().enumerate() {
            let ty = self.c.get_type_of_symbol(parameter);
            let name = parameter.name();
            self.path.push(name.to_string());
            if rest && index + 1 == parameters.len() {
                let converted = self.convert(ty);
                let converted = match converted {
                    Ty::App(ref ctor, _) if ctor == "array" => converted,
                    _ => {
                        self.note(Gap::Tuple, ty, "the rest parameter is not an array type");
                        Ty::app("array", vec![Ty::unknown()])
                    }
                };
                if top {
                    variadic = true;
                } else {
                    self.note(
                        Gap::RestInCallback,
                        ty,
                        "only an imported function can be variadic; here the rest arguments are one array",
                    );
                }
                params.push(Param { optional: None, ty: converted });
            } else if index >= required {
                let converted = self.convert_without_undefined(ty);
                let mut label = lower_ident(name);
                while params.iter().any(|param| param.optional.as_deref() == Some(&label)) {
                    label.push('_');
                }
                params.push(Param { optional: Some(label), ty: converted });
            } else {
                params.push(Param { optional: None, ty: self.convert(ty) });
            }
            self.path.pop();
        }
        self.polarity = outer;

        let result = self.c.get_return_type_of_signature(signature);
        self.path.push("result".to_string());
        let result = self.convert(result);
        self.path.pop();
        let own: Vec<String> = self.type_params[saved_params..].iter().map(|(_, name)| name.clone()).collect();
        self.type_params.truncate(saved_params);
        (Ty::Fn(params, Box::new(result)), variadic, own)
    }
}

/// Splits a union into its members that are not `null` or `undefined`.
fn split_nullish(ty: P<Type>) -> (Vec<P<Type>>, bool, bool) {
    let mut members = Vec::new();
    let mut undefined = false;
    let mut null = false;
    for &member in ty.types() {
        let flags = member.flags();
        if flags.intersects(TypeFlags::Undefined | TypeFlags::Void) {
            undefined = true;
        } else if flags.intersects(TypeFlags::Null) {
            null = true;
        } else {
            members.push(member);
        }
    }
    (members, undefined, null)
}

/// The literal a unit type stands for.
fn literal_tag(ty: P<Type>) -> Option<Tag> {
    let flags = ty.flags();
    if !flags.intersects(TypeFlags::StringLiteral | TypeFlags::NumberLiteral | TypeFlags::BooleanLiteral) {
        return None;
    }
    match ty.as_literal_type().value()? {
        LiteralValue::String(text) => Some(Tag::Str(text.to_string())),
        LiteralValue::Number(number) => Some(Tag::Num(num_literal(number.0).unwrap_or_else(|| format!("{}", number.0)))),
        LiteralValue::Boolean(value) => Some(Tag::Bool(value)),
        LiteralValue::BigInt(_) => None,
    }
}

/// Polymorphic variant tags are strings and non-negative integers.
fn poly_tag_ok(tag: &Tag) -> bool {
    match tag {
        Tag::Str(_) => true,
        Tag::Num(text) => text.bytes().all(|byte| byte.is_ascii_digit()),
        _ => false,
    }
}

fn unique_ctor(ctors: &[Ctor], base: &str) -> String {
    let mut name = base.to_string();
    let mut index = 2;
    while ctors.iter().any(|ctor| ctor.name == name) {
        name = format!("{base}{index}");
        index += 1;
    }
    name
}

/// Orders declarations so each comes after what it mentions, and groups the
/// ones that mention each other (Tarjan's strongly connected components).
fn order_decls(decls: Vec<Decl>) -> Vec<Item> {
    let index_of: HashMap<String, usize> =
        decls.iter().enumerate().map(|(index, decl)| (decl.name.clone(), index)).collect();
    let edges: Vec<Vec<usize>> = decls
        .iter()
        .map(|decl| {
            let mut targets = Vec::new();
            decl.for_each_name(&mut |name| {
                if let Some(&target) = index_of.get(name)
                    && !targets.contains(&target)
                {
                    targets.push(target);
                }
            });
            targets
        })
        .collect();

    struct Tarjan<'g> {
        edges: &'g [Vec<usize>],
        index: Vec<Option<usize>>,
        low: Vec<usize>,
        on_stack: Vec<bool>,
        stack: Vec<usize>,
        next: usize,
        groups: Vec<Vec<usize>>,
    }
    impl Tarjan<'_> {
        fn visit(&mut self, node: usize) {
            self.index[node] = Some(self.next);
            self.low[node] = self.next;
            self.next += 1;
            self.stack.push(node);
            self.on_stack[node] = true;
            for &target in &self.edges[node] {
                match self.index[target] {
                    None => {
                        self.visit(target);
                        self.low[node] = self.low[node].min(self.low[target]);
                    }
                    Some(target_index) if self.on_stack[target] => {
                        self.low[node] = self.low[node].min(target_index);
                    }
                    Some(_) => {}
                }
            }
            if Some(self.low[node]) == self.index[node] {
                let mut group = Vec::new();
                while let Some(member) = self.stack.pop() {
                    self.on_stack[member] = false;
                    group.push(member);
                    if member == node {
                        break;
                    }
                }
                group.sort_unstable();
                self.groups.push(group);
            }
        }
    }
    let count = decls.len();
    let mut tarjan = Tarjan {
        edges: &edges,
        index: vec![None; count],
        low: vec![0; count],
        on_stack: vec![false; count],
        stack: Vec::new(),
        next: 0,
        groups: Vec::new(),
    };
    for node in 0..count {
        if tarjan.index[node].is_none() {
            tarjan.visit(node);
        }
    }
    let mut slots: Vec<Option<Decl>> = decls.into_iter().map(Some).collect();
    tarjan
        .groups
        .into_iter()
        .map(|group| Item::Types(group.into_iter().filter_map(|index| slots[index].take()).collect()))
        .collect()
}
