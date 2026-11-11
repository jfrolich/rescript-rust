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
    Checker, ElementFlags, LiteralValue, ObjectFlags, Signature, SignatureFlags, SignatureKind, Type,
    TypeFlags,
};
use tsrs_compiler::Program;
use tsrs_core::P;

use crate::model::{
    Class, Ctor, Decl, DeclKind, External, Field, Item, Param, Payload, Tag, Ty, is_plain_field_name,
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
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

/// The declarations made so far. A conversion that turns out not to be
/// expressible (a generic alias, a union) is rolled back to a `Mark`: every
/// change to the maps is journaled, so a mark costs nothing and a rollback
/// costs what was done since.
#[derive(Default)]
struct State {
    by_symbol: HashMap<P<Symbol>, Named>,
    by_type: HashMap<P<Type>, Named>,
    by_shape: HashMap<String, Named>,
    used: HashSet<String>,
    pending: Vec<Decl>,
    /// The parameters of each type declared for an unnamed TypeScript type.
    anonymous_params: HashMap<String, Vec<String>>,
    /// What the values of each declared type are at run time, by type name.
    runtime: HashMap<String, Runtime>,
    /// The parameters and fields of each declared record, by type name.
    records: HashMap<String, (Vec<String>, Vec<Field>)>,
    /// The literals of each declared variant without payloads, by type name.
    literal_types: HashMap<String, Vec<Tag>>,
    notes: Vec<Note>,
    /// The notes, for telling a repeated one without a scan.
    noted: HashSet<Note>,
    journal: Vec<Undo>,
}

/// What tells the values of a declared type apart in an untagged variant.
#[derive(Clone)]
enum Runtime {
    /// A plain object: a record.
    Object,
    /// An instance of a class that `instanceof` tests for.
    Instance,
    /// Whatever the abbreviated type is.
    Alias(Ty),
    /// Nothing the compiler can test for: an abstract type or a variant.
    Unknown,
}

impl Runtime {
    fn of(decl: &Decl) -> Runtime {
        match (&decl.kind, &decl.class) {
            (_, Some(_)) => Runtime::Instance,
            (DeclKind::Record(_), None) => Runtime::Object,
            (DeclKind::Alias(ty), None) => Runtime::Alias(ty.clone()),
            (DeclKind::Abstract | DeclKind::Variant { .. }, None) => Runtime::Unknown,
        }
    }
}

enum Undo {
    Symbol(P<Symbol>, Option<Named>),
    Type(P<Type>, Option<Named>),
    Shape(String, Option<Named>),
    Used(String),
}

struct Mark {
    journal: usize,
    pending: usize,
    notes: usize,
}

impl State {
    fn mark(&self) -> Mark {
        Mark { journal: self.journal.len(), pending: self.pending.len(), notes: self.notes.len() }
    }

    fn rollback(&mut self, mark: Mark) {
        fn restore<K: std::hash::Hash + Eq>(map: &mut HashMap<K, Named>, key: K, old: Option<Named>) {
            match old {
                Some(old) => map.insert(key, old),
                None => map.remove(&key),
            };
        }
        while self.journal.len() > mark.journal {
            match self.journal.pop().expect("journal entry") {
                Undo::Symbol(key, old) => restore(&mut self.by_symbol, key, old),
                Undo::Type(key, old) => restore(&mut self.by_type, key, old),
                Undo::Shape(key, old) => restore(&mut self.by_shape, key, old),
                Undo::Used(name) => {
                    self.used.remove(&name);
                }
            }
        }
        self.pending.truncate(mark.pending);
        for note in self.notes.drain(mark.notes..) {
            self.noted.remove(&note);
        }
    }

    fn declare(&mut self, decl: Decl) {
        self.runtime.insert(decl.name.clone(), Runtime::of(&decl));
        match &decl.kind {
            DeclKind::Record(fields) if decl.class.is_none() => {
                self.records.insert(decl.name.clone(), (decl.params.clone(), fields.clone()));
            }
            DeclKind::Variant { tag: None, ctors } if ctors.iter().all(|ctor| ctor.payload == Payload::None) => {
                let literals = ctors
                    .iter()
                    .map(|ctor| ctor.tag.clone().unwrap_or_else(|| Tag::Str(ctor.name.clone())))
                    .collect();
                self.literal_types.insert(decl.name.clone(), literals);
            }
            _ => {}
        }
        self.pending.push(decl);
    }

    /// How an untagged variant recognizes a value of type `ty`: the name of
    /// a `typeof`, `"array"`, `"object"` or `"instance"`. `None` when it
    /// cannot.
    fn runtime_of(&self, ty: &Ty, depth: usize) -> Option<&'static str> {
        match ty {
            Ty::Fn(..) => Some("function"),
            Ty::Tuple(_) => Some("array"),
            Ty::Var(_) | Ty::Poly(_) => None,
            Ty::App(name, _) => match name.as_str() {
                "string" => Some("string"),
                "float" | "int" => Some("number"),
                "bigint" => Some("bigint"),
                "bool" => Some("boolean"),
                "array" => Some("array"),
                "dict" => Some("object"),
                "Symbol.t" => Some("symbol"),
                "promise" | "Date.t" | "RegExp.t" | "JsError.t" | "Map.t" | "Set.t" | "WeakMap.t" | "WeakSet.t"
                | "ArrayBuffer.t" | "DataView.t" | "Int8Array.t" | "Uint8Array.t" | "Uint8ClampedArray.t"
                | "Int16Array.t" | "Uint16Array.t" | "Int32Array.t" | "Uint32Array.t" | "Float32Array.t"
                | "Float64Array.t" | "BigInt64Array.t" | "BigUint64Array.t" => Some("instance"),
                _ => {
                    let local = name.rsplit('.').next().unwrap_or(name);
                    match self.runtime.get(local)? {
                        Runtime::Object => Some("object"),
                        Runtime::Instance => Some("instance"),
                        Runtime::Alias(target) if depth < 16 => self.runtime_of(target, depth + 1),
                        Runtime::Alias(_) | Runtime::Unknown => None,
                    }
                }
            },
        }
    }

    /// The fields of the record `ty` names, its type parameters replaced by
    /// the arguments, following abbreviations.
    fn record_fields(&self, ty: &Ty) -> Option<Vec<Field>> {
        let mut ty = ty.clone();
        for _ in 0..16 {
            let Ty::App(name, args) = &ty else {
                return None;
            };
            let local = name.rsplit('.').next().unwrap_or(name);
            if let Some((params, fields)) = self.records.get(local) {
                return Some(
                    fields
                        .iter()
                        .map(|field| Field { ty: substitute(&field.ty, params, args), ..field.clone() })
                        .collect(),
                );
            }
            match self.runtime.get(local)? {
                Runtime::Alias(target) => ty = target.clone(),
                _ => return None,
            }
        }
        None
    }

    /// What an untagged variant knows of a record with these fields.
    fn fields_shape(&self, fields: &[Field]) -> ObjectShape {
        ObjectShape::Closed(
            fields
                .iter()
                .map(|field| {
                    let literals = if field.optional { None } else { self.literals_of(&field.ty) };
                    let kind = match &literals {
                        _ if field.optional => None,
                        Some(literals) => literals_kind(literals),
                        None => self.runtime_of(&field.ty, 0),
                    };
                    FieldShape {
                        name: field.js_name.clone().unwrap_or_else(|| field.name.clone()),
                        required: !field.optional,
                        literals,
                        kind,
                    }
                })
                .collect(),
        )
    }

    /// The literals a field type stands for: a polymorphic variant, a
    /// variant without payloads, or `bool`.
    fn literals_of(&self, ty: &Ty) -> Option<Vec<Literal>> {
        self.literals_of_at(ty, 0)
    }

    fn literals_of_at(&self, ty: &Ty, depth: usize) -> Option<Vec<Literal>> {
        match ty {
            Ty::Poly(tags) => Some(
                tags.iter()
                    .map(|tag| match tag {
                        Tag::Num(text) if is_hash_number(text) => Literal::Num(text.clone()),
                        Tag::Num(text) | Tag::Str(text) => Literal::Str(text.clone()),
                        Tag::Bool(value) => Literal::Bool(*value),
                        Tag::Null | Tag::Undefined => Literal::Other,
                    })
                    .collect(),
            ),
            Ty::App(name, args) if name == "bool" && args.is_empty() => {
                Some(vec![Literal::Bool(true), Literal::Bool(false)])
            }
            Ty::App(name, _) => {
                let local = name.rsplit('.').next().unwrap_or(name);
                let Some(tags) = self.literal_types.get(local) else {
                    return match self.runtime.get(local)? {
                        Runtime::Alias(target) if depth < 16 => self.literals_of_at(target, depth + 1),
                        _ => None,
                    };
                };
                Some(
                    tags.iter()
                        .map(|tag| match tag {
                            Tag::Str(text) => Literal::Str(text.clone()),
                            Tag::Num(text) => Literal::Num(text.clone()),
                            Tag::Bool(value) => Literal::Bool(*value),
                            Tag::Null | Tag::Undefined => Literal::Other,
                        })
                        .collect(),
                )
            }
            _ => None,
        }
    }

    fn add_note(&mut self, note: Note) {
        if self.noted.insert(note.clone()) {
            self.notes.push(note);
        }
    }

    fn take_notes(&mut self) -> Vec<Note> {
        self.noted.clear();
        std::mem::take(&mut self.notes)
    }

    fn set_symbol(&mut self, symbol: P<Symbol>, named: Named) {
        let old = self.by_symbol.insert(symbol, named);
        self.journal.push(Undo::Symbol(symbol, old));
    }

    fn set_type(&mut self, ty: P<Type>, named: Named) {
        let old = self.by_type.insert(ty, named);
        self.journal.push(Undo::Type(ty, old));
    }

    fn set_shape(&mut self, key: String, named: Named) {
        let old = self.by_shape.insert(key.clone(), named);
        self.journal.push(Undo::Shape(key, old));
    }

    fn use_name(&mut self, name: String) {
        if self.used.insert(name.clone()) {
            self.journal.push(Undo::Used(name));
        }
    }
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
    /// How many named declarations are being converted, nested.
    declaration_depth: usize,
    /// The unnamed types being converted, with the name one was given when
    /// it was reached inside itself.
    unnamed_in_progress: HashMap<P<Type>, Option<String>>,
    /// The declared type of the interface or class being declared: there it
    /// is the declaration's body, anywhere else a reference to it.
    declaring: Option<P<Type>>,
    /// The modules the file imports from, by specifier.
    modules: Vec<(String, P<Symbol>)>,
    /// The classes those modules export, with the specifier and the export
    /// name: where `instanceof` finds the class at run time. Filled on first
    /// use.
    class_exports: Option<HashMap<P<Symbol>, (String, String)>>,
    /// The fields of each class declared as a record.
    class_fields: HashMap<P<Symbol>, Vec<Field>>,
    /// The superclass each declared class names.
    declared_parents: HashMap<P<Symbol>, P<Symbol>>,
    /// The classes whose declaration states the class.
    declared_classes: HashSet<P<Symbol>>,
    /// [`object_groups`] of the plain object members of a union, by members.
    object_groups: HashMap<Vec<P<Type>>, Option<Vec<Vec<usize>>>>,
}

const MAX_DEPTH: usize = 48;
/// How many named declarations deep a conversion goes. Each declaration
/// stands on its own, so it starts a new count of [`MAX_DEPTH`]; a recursive
/// group of many declarations, such as a syntax tree, nests this deep.
const MAX_DECLARATION_DEPTH: usize = 512;

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
            state: State::default(),
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
            declaration_depth: 0,
            unnamed_in_progress: HashMap::new(),
            declaring: None,
            modules: Vec::new(),
            class_exports: None,
            class_fields: HashMap::new(),
            declared_parents: HashMap::new(),
            declared_classes: HashSet::new(),
            object_groups: HashMap::new(),
        }
    }

    /// The modules the requests import from.
    pub(crate) fn set_modules(&mut self, modules: Vec<(String, P<Symbol>)>) {
        self.modules = modules;
        self.class_exports = None;
    }

    // ----- classes --------------------------------------------------------

    /// Where the class `symbol` is found at run time: its path and the
    /// module that exports it, or a global path. `None` for a class nothing
    /// names: `instanceof` cannot test for it.
    fn class_ref(&mut self, symbol: P<Symbol>) -> Option<(String, Option<String>)> {
        if self.is_lib_symbol(symbol) {
            // A global with a constructor: `declare var URL: {prototype: URL; new(...): URL}`.
            let name = symbol.name();
            // Not classes to recognize values by: every object is an
            // `Object`, arrays have `Array.isArray`, and the wrappers of
            // primitives are not what the primitive types hold.
            if matches!(
                name,
                "Object" | "Function" | "Array" | "ReadonlyArray" | "String" | "Number" | "Boolean" | "Symbol" | "BigInt"
            ) || !symbol.flags().intersects(SymbolFlags::Variable | SymbolFlags::Class)
            {
                return None;
            }
            let statics = self.c.get_type_of_symbol(symbol);
            return self
                .c
                .get_property_of_type(statics, "prototype")
                .is_some()
                .then(|| (name.to_string(), None));
        }
        if !symbol.flags().intersects(SymbolFlags::Class) {
            return None;
        }
        if self.class_exports.is_none() {
            let mut exports: HashMap<P<Symbol>, (String, String)> = HashMap::new();
            for (module, module_symbol) in self.modules.clone() {
                for export in self.c.get_exports_of_module_exported(module_symbol) {
                    let target = self.c.skip_alias(export);
                    if target.flags().intersects(SymbolFlags::Class) {
                        exports.entry(target).or_insert_with(|| (module.clone(), export.name().to_string()));
                    }
                }
            }
            self.class_exports = Some(exports);
        }
        if let Some((module, name)) = self.class_exports.as_ref().and_then(|exports| exports.get(&symbol)) {
            return Some((name.clone(), Some(module.clone())));
        }
        // A class of an ambient module: `declare module "node:stream" { class
        // Readable {} }`, also inside a namespace the module exports with
        // `export =`.
        let mut node = symbol.declarations().first().copied();
        while let Some(at) = node {
            if tsrs_ast::is_ambient_module(at) {
                let module_symbol = self.c.get_symbol_of_declaration_exported(at)?;
                let module = module_symbol.name().trim_matches('"').to_string();
                let exported = self
                    .c
                    .get_exports_of_module_exported(module_symbol)
                    .into_iter()
                    .find(|&export| self.c.skip_alias(export) == symbol)?;
                return Some((exported.name().to_string(), Some(module)));
            }
            node = at.parent();
        }
        None
    }

    /// The class `symbol` extends, when that class can be named at run time
    /// too, with its instance type.
    fn base_class(&mut self, symbol: P<Symbol>) -> Option<(P<Symbol>, P<Type>)> {
        let declared = self.c.get_declared_type_of_symbol(symbol);
        let bases: Vec<P<Type>> = self.c.get_base_types_exported(declared).to_vec();
        for base in bases {
            if let Some(parent) = base.symbol()
                && parent != symbol
                && self.class_ref(parent).is_some()
            {
                return Some((parent, base));
            }
        }
        None
    }

    /// The class of a record declared for the class `symbol`. The superclass
    /// is named when the record has its fields exactly, which the compiler
    /// requires of a subclass; a class that narrows a member stands alone.
    fn record_class(&mut self, symbol: P<Symbol>, own: &Ty, fields: &[Field]) -> Option<Class> {
        let (path, module) = self.class_ref(symbol)?;
        self.class_fields.insert(symbol, fields.to_vec());
        let mut parent = None;
        if let Some((parent_symbol, base)) = self.base_class(symbol)
            && !self.is_lib_symbol(parent_symbol)
            && self.c.get_type_arguments(base).is_empty()
        {
            let parent_ty = self.convert(base);
            // A method that returns `this` returns the subclass in the
            // subclass, which is a subtype of what the superclass has.
            let inherits = self.class_fields.get(&parent_symbol).is_some_and(|parent_fields| {
                parent_fields.iter().all(|field| {
                    fields.contains(field)
                        || fields.contains(&Field { ty: returning(&field.ty, &parent_ty, own), ..field.clone() })
                })
            });
            if inherits && matches!(parent_ty, Ty::App(..)) {
                self.declared_parents.insert(symbol, parent_symbol);
                parent = Some(parent_ty);
            }
        }
        self.declared_classes.insert(symbol);
        Some(Class { path, module, parent })
    }

    /// Whether the classes of a union can be cases of one variant: when one
    /// extends another, the declarations say so, and the subclass is then
    /// tested first.
    fn class_cases_agree(&mut self, classes: &[P<Symbol>]) -> bool {
        for &class in classes {
            let mut declared: Vec<P<Symbol>> = Vec::new();
            let mut at = class;
            while let Some(&parent) = self.declared_parents.get(&at) {
                if declared.contains(&parent) {
                    break;
                }
                declared.push(parent);
                at = parent;
            }
            let mut at = class;
            for _ in 0..32 {
                let Some((parent, _)) = self.base_class(at) else { break };
                if classes.contains(&parent) && !declared.contains(&parent) {
                    return false;
                }
                at = parent;
            }
        }
        true
    }

    // ----- requests -------------------------------------------------------

    pub(crate) fn begin_request(&mut self, scope: &[String]) {
        self.scope = scope.to_vec();
        self.state.pending.clear();
        self.state.take_notes();
        // No mark outlives a request.
        self.state.journal.clear();
    }

    /// Records an export of a whole-module import that has no ReScript form.
    pub(crate) fn skipped_export(&mut self, export: &str, what: &str) {
        self.begin_subject(export);
        self.note_text(Gap::ValueObject, export.to_string(), what);
    }

    pub(crate) fn take_notes(&mut self) -> Vec<Note> {
        self.state.take_notes()
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
        // `type t<'a> = stack<'a>` for a generic class.
        let class_params = self.c.get_local_type_parameters_of_class_or_interface_or_type_alias_exported(symbol);
        for &param in &class_params {
            let name = lower_ident(param.symbol().map_or("t", |symbol| symbol.name()));
            self.type_params.push((param, name));
        }
        let instance_ty = self.convert(instance);
        let params: Vec<String> = self.type_params.drain(..).map(|(_, name)| name).collect();
        let mut items = vec![Item::Types(vec![Decl {
            name: "t".to_string(),
            params,
            kind: DeclKind::Alias(instance_ty),
            ts: None,
            class: None,
        }])];
        let statics = self.c.get_type_of_symbol(symbol);
        let constructs = self.c.get_signatures_of_type(statics, SignatureKind::Construct);
        // An abstract class has a construct signature nobody may call.
        if constructs.first().is_some_and(|signature| !signature.flags().intersects(SignatureFlags::Abstract)) {
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
        self.state.use_name(local.to_string());
        self.state.declare(Decl {
            name: local.to_string(),
            params,
            kind: DeclKind::Alias(target),
            ts: None,
            class: None,
        });
        Ok(())
    }

    // ----- names ----------------------------------------------------------

    fn fresh_type_name(&mut self, base: &str) -> String {
        let base = lower_ident(base);
        let mut name = base.clone();
        let mut index = 2;
        while self.state.used.contains(&name) || crate::model::is_builtin_type(&name) {
            name = format!("{base}{index}");
            index += 1;
        }
        self.state.use_name(name.clone());
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
        self.state.add_note(note);
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
            // The type's parameters are the variables it mentions, under the
            // names they had where it was declared. Somewhere they are not
            // in scope, the type is declared again.
            let params = self.state.anonymous_params.get(&named.name).cloned().unwrap_or_default();
            if params.iter().all(|param| self.type_params.iter().any(|(_, name)| name == param)) {
                return Ty::App(self.reference(&named), params.into_iter().map(Ty::Var).collect());
            }
        }
        // An unnamed type can contain itself, through a union in one of its
        // fields (`elements: (BindingPattern | null)[]` in a member of
        // `BindingPattern`). Reached again while it is converted, it is given
        // a name, which the outer conversion then declares.
        let guarded = ty.flags().intersects(TypeFlags::Union | TypeFlags::Intersection);
        if !guarded {
            return match self.structure(ty) {
                Structure::Ty(converted) => converted,
                Structure::Decl(kind) => self.declare_anonymous(ty, kind),
            };
        }
        if let Some(reserved) = self.unnamed_in_progress.get(&ty).cloned() {
            if !self.type_params.is_empty() {
                self.note(Gap::Depth, ty, "the type contains itself");
                return Ty::unknown();
            }
            let name = match reserved {
                Some(name) => name,
                None => {
                    let name = self.fresh_type_name(&self.context_name());
                    self.unnamed_in_progress.insert(ty, Some(name.clone()));
                    name
                }
            };
            return Ty::name(&name);
        }
        self.unnamed_in_progress.insert(ty, None);
        let structure = self.structure(ty);
        let reserved = self.unnamed_in_progress.remove(&ty).flatten();
        match (structure, reserved) {
            (Structure::Ty(converted), None) => converted,
            (Structure::Decl(kind), None) => self.declare_anonymous(ty, kind),
            (structure, Some(name)) => {
                let kind = match structure {
                    Structure::Ty(converted) => DeclKind::Alias(converted),
                    Structure::Decl(kind) => kind,
                };
                let kind = if free_variables(&kind).is_empty() { kind } else { DeclKind::Abstract };
                let named = Named { scope: self.scope.clone(), name: name.clone(), params: 0 };
                self.state.set_type(ty, named);
                self.state.anonymous_params.insert(name.clone(), Vec::new());
                self.state.declare(Decl { name: name.clone(), params: Vec::new(), kind, ts: None, class: None });
                Ty::name(&name)
            }
        }
    }

    /// Declares a record or variant for a type TypeScript did not name. The
    /// type variables it mentions become its parameters.
    fn declare_anonymous(&mut self, ty: P<Type>, kind: DeclKind) -> Ty {
        let params = free_variables(&kind);
        let args = |params: &[String]| params.iter().cloned().map(Ty::Var).collect::<Vec<Ty>>();
        let probe = Decl { name: String::new(), params, kind, ts: None, class: None };
        let key = shape_key(&probe);
        if let Some(named) = self.state.by_shape.get(&key).cloned() {
            self.state.set_type(ty, named.clone());
            return Ty::App(self.reference(&named), args(&probe.params));
        }
        let name = self.fresh_type_name(&self.context_name());
        let named = Named { scope: self.scope.clone(), name: name.clone(), params: probe.params.len() };
        self.state.set_type(ty, named.clone());
        self.state.set_shape(key, named);
        let reference = Ty::App(name.clone(), args(&probe.params));
        self.state.anonymous_params.insert(name.clone(), probe.params.clone());
        self.state.declare(Decl { name, ..probe });
        reference
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
        let mark = (is_alias && !params.is_empty()).then(|| self.state.mark());

        let name = match local {
            Some(local) => {
                self.state.use_name(local.to_string());
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
        self.state.set_symbol(
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
        let saved_depth = self.depth;
        if self.declaration_depth < MAX_DECLARATION_DEPTH {
            self.depth = 0;
        }
        self.declaration_depth += 1;

        let declared = self.c.get_declared_type_of_symbol(symbol);
        let is_object_declaration = symbol.flags().intersects(SymbolFlags::Class | SymbolFlags::Interface);
        // A union inside the declaration may have the declaration itself as
        // a member, before it is known what it becomes: a record, unless it
        // can be called.
        if is_object_declaration
            && self.c.get_signatures_of_type(declared, SignatureKind::Call).is_empty()
            && self.c.get_signatures_of_type(declared, SignatureKind::Construct).is_empty()
        {
            self.state.runtime.insert(name.clone(), Runtime::Object);
        }
        let saved_declaring =
            std::mem::replace(&mut self.declaring, if is_object_declaration { Some(declared) } else { None });
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
        self.depth = saved_depth;
        self.declaration_depth -= 1;

        if let Some(mark) = mark
            && deferred
        {
            self.state.rollback(mark);
            self.opaque_aliases.insert(symbol);
            return false;
        }
        // A class that can be named at run time is declared one, so that it
        // can be a case of a union.
        let class = match &kind {
            DeclKind::Record(fields) if symbol.flags().intersects(SymbolFlags::Class) => {
                let own = Ty::App(name.clone(), param_names.iter().cloned().map(Ty::Var).collect());
                self.record_class(symbol, &own, fields)
            }
            _ => None,
        };
        self.state.declare(Decl { name, params: param_names, kind, ts: None, class });
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
            "Iterator" | "IterableIterator" | "IteratorObject" | "Generator" | "ArrayIterator"
            | "MapIterator" | "SetIterator" => {
                Ty::app("Iterator.t", vec![arg(self, 0), Ty::unknown(), Ty::unknown()])
            }
            "AsyncIterator" | "AsyncIterableIterator" | "AsyncGenerator" | "AsyncIteratorObject" => {
                Ty::app("AsyncIterator.t", vec![arg(self, 0), Ty::unknown(), Ty::unknown()])
            }
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
                self.state.set_symbol(symbol, named);
                // A global class (`Element`, `URL`) is declared one, with the
                // class it extends.
                let class = match self.class_ref(symbol) {
                    Some((path, module)) => {
                        self.declared_classes.insert(symbol);
                        let parent = match self.base_class(symbol) {
                            Some((parent, _)) => {
                                self.declared_parents.insert(symbol, parent);
                                Some(self.lib_type(parent, &[]))
                            }
                            None => None,
                        };
                        Some(Class { path, module, parent })
                    }
                    None => None,
                };
                self.state.declare(Decl {
                    name: type_name.clone(),
                    params: Vec::new(),
                    kind: DeclKind::Abstract,
                    ts: Some(name.to_string()),
                    class,
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
                // Private `#names` and symbol-keyed members carry TypeScript's
                // internal name prefix; neither is a string-named property.
                if name.starts_with(tsrs_ast::INTERNAL_SYMBOL_NAME_PREFIX) || name.starts_with("__@") || name.starts_with('#') || name == "prototype" {
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
            if generic && !first.type_parameters().is_empty() {
                self.note(
                    Gap::GenericCallback,
                    ty,
                    "the callback's own type parameters become type parameters of the import, so the callback is checked for one type, not for all",
                );
            }
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
            // A renamed field must not take the name another property has
            // in JavaScript (`Comment` beside `comment`): the compiler
            // rejects a record where one name is defined twice.
            let taken = |name: &str| {
                fields.iter().any(|field: &Field| field.name == name || field.js_name.as_deref() == Some(name))
                    || name != js_name && properties.iter().any(|other| other.name() == name)
            };
            while taken(&name) {
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
            // `string & {}` is `string`: the `{}` only keeps the literals of a
            // union apart for the editor.
            let branded = ty.types().iter().any(|&member| {
                member != primitive && !self.c.get_properties_of_type(member).is_empty()
            });
            if branded {
                self.note(Gap::Intersection, ty, "the brand is dropped; the primitive type is used");
            }
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

        // `"on" | "off" | (string & {})` accepts any string: the literals are
        // suggestions for the editor. The same for numbers.
        for (primitive, literal) in [
            (TypeFlags::String, TypeFlags::StringLiteral),
            (TypeFlags::Number, TypeFlags::NumberLiteral),
        ] {
            let is_primitive = |member: &P<Type>| {
                member.flags().intersects(primitive)
                    || (member.flags().intersects(TypeFlags::Intersection)
                        && member.types().iter().any(|part| part.flags().intersects(primitive)))
            };
            if members.iter().any(is_primitive) {
                members.retain(|member| !member.flags().intersects(literal));
            }
        }
        if let [one] = members.as_slice()
            && !whole_boolean
        {
            return Structure::Ty(self.convert(*one));
        }

        // The members of one enum (what is left of `Priority | undefined`):
        // the enum's own type.
        if !whole_boolean {
            let enum_of = |member: &P<Type>| {
                member
                    .flags()
                    .intersects(TypeFlags::EnumLiteral)
                    .then(|| member.symbol().and_then(|symbol| symbol.parent()))
                    .flatten()
                    .filter(|parent| parent.flags().intersects(SymbolFlags::Enum))
            };
            if let Some(first) = enum_of(&members[0])
                && members.iter().all(|member| enum_of(member).is_some_and(|parent| parent == first))
            {
                return Structure::Ty(self.symbol_type(first, &[]));
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
                    // `{ok: true, ...} | {ok: false, ...}` reads as `Ok` and `NotOk`.
                    Tag::Bool(true) => upper_ident(name),
                    Tag::Bool(false) => format!("Not{}", upper_ident(name)),
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
        // First whether the members can be told apart at run time, from the
        // TypeScript types alone: converting a member declares what it
        // mentions, which is wasted on a union that is then given up.
        // A member's kind is what tells it apart: a `typeof`, `Array.isArray`
        // or a class for `instanceof`. A variant has one case per kind.
        let mut kinds: HashSet<String> = HashSet::new();
        if whole_boolean {
            kinds.insert("boolean".to_string());
        }
        let mut bases: Vec<Option<&'static str>> = Vec::with_capacity(members.len());
        // The members that are classes declared for this file.
        let mut classes: Vec<P<Symbol>> = Vec::new();
        // The members that are plain objects.
        let mut plain_objects: Vec<P<Type>> = Vec::new();
        for &member in members {
            if literal_tag(member).is_some() {
                bases.push(None);
                continue;
            }
            let flags = member.flags();
            let (kind, base): (String, &'static str) = if flags.intersects(TypeFlags::String | TypeFlags::TemplateLiteral | TypeFlags::StringMapping) {
                ("string".into(), "String")
            } else if flags.intersects(TypeFlags::Number) {
                ("number".into(), "Number")
            } else if flags.intersects(TypeFlags::BigInt) {
                ("bigint".into(), "BigInt")
            } else if flags.intersects(TypeFlags::Boolean) {
                ("boolean".into(), "Boolean")
            } else if flags.intersects(TypeFlags::ESSymbol | TypeFlags::UniqueESSymbol) {
                ("symbol".into(), "Symbol")
            } else if flags.intersects(TypeFlags::Object) {
                if self.c.is_array_or_tuple_type(member) {
                    ("array".into(), "Array")
                } else if !self.c.get_signatures_of_type(member, SignatureKind::Call).is_empty() {
                    ("function".into(), "Function")
                } else {
                    match member.symbol() {
                        Some(symbol) if self.is_lib_symbol(symbol) => match symbol.name() {
                            "Date" => ("Date".into(), "Date"),
                            "RegExp" => ("RegExp".into(), "RegExp"),
                            "Promise" => ("Promise".into(), "Promise"),
                            "Map" | "ReadonlyMap" => ("Map".into(), "Map"),
                            "Set" | "ReadonlySet" => ("Set".into(), "Set"),
                            "WeakMap" => ("WeakMap".into(), "WeakMap"),
                            "WeakSet" => ("WeakSet".into(), "WeakSet"),
                            "Error" | "TypeError" | "RangeError" | "SyntaxError" | "ReferenceError"
                            | "EvalError" | "URIError" | "AggregateError" => ("Error".into(), "Error"),
                            "ArrayBuffer" => ("ArrayBuffer".into(), "ArrayBuffer"),
                            "DataView" => ("DataView".into(), "DataView"),
                            name @ ("Int8Array" | "Uint8Array" | "Uint8ClampedArray" | "Int16Array"
                            | "Uint16Array" | "Int32Array" | "Uint32Array" | "Float32Array"
                            | "Float64Array" | "BigInt64Array" | "BigUint64Array") => {
                                (name.to_string(), "TypedArray")
                            }
                            name => match self.class_ref(symbol) {
                                Some(_) => {
                                    classes.push(symbol);
                                    (name.to_string(), "Object")
                                }
                                None => ("object".into(), "Object"),
                            },
                        },
                        Some(symbol) => match self.class_ref(symbol) {
                            Some((path, module)) => {
                                classes.push(symbol);
                                (format!("{path} of {}", module.unwrap_or_default()), "Object")
                            }
                            None => ("object".into(), "Object"),
                        },
                        None => ("object".into(), "Object"),
                    }
                }
            } else if flags.intersects(TypeFlags::Intersection)
                && member.types().iter().all(|&part| {
                    part.flags().intersects(TypeFlags::Object)
                        && !self.c.is_array_or_tuple_type(part)
                        && self.c.get_signatures_of_type(part, SignatureKind::Call).is_empty()
                })
            {
                // An intersection of object types is one record.
                ("object".into(), "Object")
            } else {
                return None;
            };
            // Several plain objects may be told apart by their fields; that
            // is checked once they are converted.
            let plain_object = kind == "object";
            if !kinds.insert(kind) && !plain_object {
                return None;
            }
            if plain_object {
                plain_objects.push(member);
            }
            bases.push(Some(base));
        }
        // Converting a member declares what it mentions, so first a check on
        // the TypeScript types that an order of the plain objects can exist.
        // Members that no check tells apart (they share a tag and differ
        // only inside a field) become one case: `group_of` maps each such
        // member to its group.
        let mut group_of: HashMap<P<Type>, usize> = HashMap::new();
        if plain_objects.len() > 1 {
            let groups = match self.object_groups.get(&plain_objects) {
                Some(groups) => groups.clone(),
                None => {
                    let shapes: Vec<ObjectShape> =
                        plain_objects.iter().map(|&member| self.ts_object_shape(member)).collect();
                    let groups = object_groups(shapes);
                    self.object_groups.insert(plain_objects.clone(), groups.clone());
                    groups
                }
            }?;
            for (group, indices) in groups.iter().enumerate() {
                if indices.len() > 1 {
                    for &index in indices {
                        group_of.insert(plain_objects[index], group);
                    }
                }
            }
        }
        // For each group, its case and its members.
        let mut group_cases: HashMap<usize, (usize, Vec<P<Type>>)> = HashMap::new();
        // The TypeScript member of each case with a payload.
        let mut ctor_members: Vec<Option<P<Type>>> = Vec::new();
        // The TypeScript shape of each case made of several members.
        let mut merged_shapes: HashMap<usize, ObjectShape> = HashMap::new();

        let mut ctors: Vec<Ctor> = Vec::new();
        if whole_boolean {
            ctors.push(Ctor { name: "Boolean".to_string(), tag: None, payload: Payload::Ty(Ty::name("bool")) });
        }
        let saved_free = std::mem::replace(&mut self.free_vars, false);
        let mark = self.state.mark();
        for (&member, base) in members.iter().zip(bases) {
            let Some(base) = base else {
                let tag = literal_tag(member).expect("a literal member");
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
            };
            self.path.push(base.to_string());
            let payload = self.convert(member);
            self.path.pop();
            // The member's ReScript type is what the compiler tests for.
            let expected: &[&str] = match base {
                "String" => &["string"],
                "Number" => &["number"],
                "BigInt" => &["bigint"],
                "Boolean" => &["boolean"],
                "Symbol" => &["symbol"],
                "Array" => &["array"],
                "Function" => &["function"],
                "Object" => &["object", "instance"],
                _ => &["instance"],
            };
            if !self.state.runtime_of(&payload, 0).is_some_and(|found| expected.contains(&found)) {
                self.free_vars = saved_free;
                self.state.rollback(mark);
                // A union given up is not converted again where it recurs.
                if plain_objects.len() > 1 {
                    self.object_groups.insert(plain_objects, None);
                }
                return None;
            }
            // An object member is named after its type: `User(user)`.
            let base = match (&payload, base) {
                (Ty::App(name, _), "Object") if !name.contains('.') && name != "dict" => capitalize(name),
                (Ty::App(name, _), "TypedArray") => name.trim_end_matches(".t").to_string(),
                _ => base.to_string(),
            };
            if let Some(&group) = group_of.get(&member) {
                if let Some((_, grouped)) = group_cases.get_mut(&group) {
                    grouped.push(member);
                    continue;
                }
                group_cases.insert(group, (ctors.len(), vec![member]));
            }
            // A member of the same shape as an earlier one is that member.
            if expected == ["object", "instance"]
                && ctors.iter().any(|ctor| match &ctor.payload {
                    Payload::Ty(other) => {
                        *other == payload
                            || self.state.runtime_of(other, 0) == Some("object")
                                && self.state.record_fields(other).is_some_and(|fields| {
                                    Some(fields) == self.state.record_fields(&payload)
                                })
                    }
                    _ => false,
                })
            {
                continue;
            }
            let name = unique_ctor(&ctors, &base);
            ctors.push(Ctor { name, tag: None, payload: Payload::Ty(payload) });
            ctor_members.resize(ctors.len() - 1, None);
            ctor_members.push(Some(member));
        }
        ctor_members.resize(ctors.len(), None);
        // The members of a group are one case, an inline record with the
        // fields of all of them.
        // Their fields are read from TypeScript: a member's record may still
        // be being declared, in a recursive group. The case's record is named,
        // and the name is taken first, so that a union of the same members
        // inside one of the fields refers to it.
        let mut groups: Vec<(usize, Vec<P<Type>>)> = group_cases.into_values().collect();
        groups.sort_by_key(|(index, _)| *index);
        let mut give_up = false;
        for (index, grouped) in groups {
            if grouped.len() < 2 {
                continue;
            }
            let key = format!(
                "merged {}",
                grouped.iter().map(|member| member.to_bits().to_string()).collect::<Vec<_>>().join(" ")
            );
            let named = match self.state.by_shape.get(&key).cloned() {
                Some(named) => named,
                None => {
                    let name = self.fresh_type_name(&format!("{}Case", ctors[index].name));
                    let named = Named { scope: self.scope.clone(), name: name.clone(), params: 0 };
                    self.state.set_shape(key, named.clone());
                    self.path.push(ctors[index].name.clone());
                    let records: Vec<Vec<Field>> = grouped
                        .iter()
                        .map(|&member| {
                            let properties = self.visible_properties(member);
                            self.fields(&properties, None)
                        })
                        .collect();
                    self.path.pop();
                    let case = ctors[index].name.clone();
                    let fields = self.merge_fields(&case, &records);
                    // The record has no parameters of its own: a case whose
                    // fields mention type variables is not merged.
                    let kind = DeclKind::Record(fields);
                    if !free_variables(&kind).is_empty() {
                        give_up = true;
                        break;
                    }
                    self.state.declare(Decl { name, params: Vec::new(), kind, ts: None, class: None });
                    named
                }
            };
            merged_shapes.insert(index, {
                let shapes: Vec<ObjectShape> = grouped.iter().map(|&member| self.ts_object_shape(member)).collect();
                shapes.iter().skip(1).fold(shapes[0].clone(), |merged, shape| merge_shapes(&merged, shape))
            });
            ctors[index].payload = Payload::Ty(Ty::App(self.reference(&named), Vec::new()));
        }
        self.free_vars = saved_free;
        if give_up {
            self.state.rollback(mark);
            self.object_groups.insert(plain_objects, None);
            return None;
        }
        // Several plain objects need an order in which the compiler tells
        // them apart by their fields.
        // A record still being declared has no fields yet; its TypeScript
        // members say what they will be.
        let mut objects: Vec<ObjectShape> = Vec::new();
        for (index, (ctor, member)) in ctors.iter().zip(&ctor_members).enumerate() {
            let shape = match &ctor.payload {
                Payload::Ty(Ty::App(name, _)) if name == "dict" => ObjectShape::Open,
                Payload::Ty(ty) if self.state.runtime_of(ty, 0) == Some("object") => {
                    match (self.state.record_fields(ty), merged_shapes.get(&index), member) {
                        (Some(fields), _, _) => self.state.fields_shape(&fields),
                        (None, Some(shape), _) => shape.clone(),
                        (None, None, Some(member)) => self.ts_object_shape(*member),
                        (None, None, None) => ObjectShape::Open,
                    }
                }
                Payload::Record(fields) => self.state.fields_shape(fields),
                _ => continue,
            };
            objects.push(shape);
        }
        if objects.len() > 1 && !objects_ordered(objects) {
            self.state.rollback(mark);
            self.object_groups.insert(plain_objects, None);
            return None;
        }
        // Each class member was declared a class, and a class that extends
        // another member says so: the compiler then tests it first. If not,
        // the members cannot be told apart after all.
        if classes.iter().any(|class| !self.declared_classes.contains(class))
            || !self.class_cases_agree(&classes)
        {
            self.state.rollback(mark);
            return None;
        }
        Some(DeclKind::Variant { tag: None, ctors })
    }

    /// The fields of one case made of several members: every field any of
    /// them has, optional unless all have it. A field whose type differs is
    /// the union of the literals when all are literals, otherwise `unknown`,
    /// with a note.
    fn merge_fields(&mut self, case: &str, records: &[Vec<Field>]) -> Vec<Field> {
        let js = |field: &Field| field.js_name.clone().unwrap_or_else(|| field.name.clone());
        let mut merged: Vec<Field> = Vec::new();
        for record in records {
            for field in record {
                if !merged.iter().any(|other| js(other) == js(field)) {
                    merged.push(field.clone());
                }
            }
        }
        for field in &mut merged {
            let key = js(field);
            let versions: Vec<Option<&Field>> =
                records.iter().map(|record| record.iter().find(|other| js(other) == key)).collect();
            field.optional = versions.iter().any(|version| version.is_none_or(|version| version.optional));
            let types: Vec<&Field> = versions.into_iter().flatten().collect();
            if types.iter().all(|version| version.ty == field.ty && version.poly == field.poly) {
                continue;
            }
            let tags: Option<Vec<Tag>> = types
                .iter()
                .map(|version| match &version.ty {
                    Ty::Poly(tags) => Some(tags.clone()),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()
                .map(|lists| {
                    let mut all: Vec<Tag> = Vec::new();
                    for tag in lists.into_iter().flatten() {
                        if !all.contains(&tag) {
                            all.push(tag);
                        }
                    }
                    all
                });
            field.poly = Vec::new();
            field.ty = match tags {
                Some(tags) => Ty::Poly(tags),
                None => {
                    self.note_text(
                        Gap::Union,
                        key.clone(),
                        &format!("the members merged into case {case} have different types for this field"),
                    );
                    Ty::unknown()
                }
            };
        }
        merged
    }

    /// What the TypeScript type of a plain object member says about the
    /// fields its converted record will have, for an early check that the
    /// members of a union can be told apart.
    fn ts_object_shape(&mut self, member: P<Type>) -> ObjectShape {
        let properties = self.visible_properties(member);
        if properties.is_empty() {
            return ObjectShape::Open;
        }
        let fields = properties
            .iter()
            .map(|&property| {
                let optional = property.flags().intersects(SymbolFlags::Optional);
                let ty = self.c.get_type_of_symbol(property);
                let (literals, kind) = if optional { (None, None) } else { self.ts_field_values(ty) };
                FieldShape { name: property.name().to_string(), required: !optional, literals, kind }
            })
            .collect();
        ObjectShape::Closed(fields)
    }

    /// The literals and the kind of the values of a field's TypeScript type.
    fn ts_field_values(&mut self, ty: P<Type>) -> (Option<Vec<Literal>>, Option<&'static str>) {
        let flags = ty.flags();
        let literal = |tag: Tag| match tag {
            Tag::Num(text) if is_hash_number(&text) => Literal::Num(text),
            Tag::Num(text) | Tag::Str(text) => Literal::Str(text),
            Tag::Bool(value) => Literal::Bool(value),
            Tag::Null | Tag::Undefined => Literal::Other,
        };
        if flags.intersects(TypeFlags::Boolean | TypeFlags::BooleanLiteral) {
            return (Some(vec![Literal::Bool(true), Literal::Bool(false)]), Some("boolean"));
        }
        let tags: Option<Vec<Tag>> = if flags.intersects(TypeFlags::Union) {
            ty.types().iter().map(|&member| literal_tag(member)).collect()
        } else {
            literal_tag(ty).map(|tag| vec![tag])
        };
        if let Some(tags) = tags {
            let literals: Vec<Literal> = tags.into_iter().map(literal).collect();
            let kind = literals_kind(&literals);
            return (Some(literals), kind);
        }
        let kind = if flags.intersects(TypeFlags::String | TypeFlags::TemplateLiteral | TypeFlags::StringMapping) {
            Some("string")
        } else if flags.intersects(TypeFlags::Number) {
            Some("number")
        } else if flags.intersects(TypeFlags::BigInt) {
            Some("bigint")
        } else if flags.intersects(TypeFlags::Object) {
            if self.c.is_array_or_tuple_type(ty) {
                Some("array")
            } else if !self.c.get_signatures_of_type(ty, SignatureKind::Call).is_empty() {
                Some("function")
            } else {
                // A plain object or a class instance; the check is kept
                // permissive, the converted types decide.
                Some("object")
            }
        } else {
            None
        };
        (None, kind)
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
/// The type variables a declaration body mentions and does not bind, in
/// the order they appear.
fn free_variables(kind: &DeclKind) -> Vec<String> {
    fn of_ty(ty: &Ty, bound: &[String], out: &mut Vec<String>) {
        match ty {
            Ty::Var(name) => {
                if !bound.contains(name) && !out.contains(name) {
                    out.push(name.clone());
                }
            }
            Ty::App(_, args) | Ty::Tuple(args) => args.iter().for_each(|arg| of_ty(arg, bound, out)),
            Ty::Fn(params, result) => {
                params.iter().for_each(|param| of_ty(&param.ty, bound, out));
                of_ty(result, bound, out);
            }
            Ty::Poly(_) => {}
        }
    }
    fn of_fields(fields: &[Field], out: &mut Vec<String>) {
        for field in fields {
            of_ty(&field.ty, &field.poly, out);
        }
    }
    let mut out = Vec::new();
    match kind {
        DeclKind::Abstract => {}
        DeclKind::Alias(ty) => of_ty(ty, &[], &mut out),
        DeclKind::Record(fields) => of_fields(fields, &mut out),
        DeclKind::Variant { ctors, .. } => {
            for ctor in ctors {
                match &ctor.payload {
                    Payload::None => {}
                    Payload::Ty(ty) => of_ty(ty, &[], &mut out),
                    Payload::Record(fields) => of_fields(fields, &mut out),
                }
            }
        }
    }
    out
}

/// `ty` with `from` replaced by `to` where a value of the type comes out:
/// the type itself, the elements of a tuple and what a function returns.
fn returning(ty: &Ty, from: &Ty, to: &Ty) -> Ty {
    if ty == from {
        return to.clone();
    }
    match ty {
        Ty::Tuple(items) => Ty::Tuple(items.iter().map(|item| returning(item, from, to)).collect()),
        Ty::Fn(params, result) => Ty::Fn(params.clone(), Box::new(returning(result, from, to))),
        Ty::App(..) | Ty::Var(_) | Ty::Poly(_) => ty.clone(),
    }
}

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

/// A JavaScript literal a field of an object member may be, for telling
/// object members apart.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Literal {
    Str(String),
    /// A number as written.
    Num(String),
    Bool(bool),
    /// `null` or `undefined`, which no check compares with.
    Other,
}

/// What a field of an object member says about its values.
#[derive(Clone, Debug, PartialEq)]
struct FieldShape {
    /// The JavaScript name.
    name: String,
    required: bool,
    literals: Option<Vec<Literal>>,
    /// As [`State::runtime_of`]: `"string"`, `"array"`, `"instance"`, ...
    kind: Option<&'static str>,
}

/// An object member: its fields, or an open object.
#[derive(Clone, Debug, PartialEq)]
enum ObjectShape {
    Closed(Vec<FieldShape>),
    Open,
}

/// One check on a field: presence, literals or kind.
#[derive(Clone, Debug)]
enum Check {
    Present(String),
    Literals(String, Vec<Literal>),
    Kind(String, &'static str),
}

impl Check {
    fn field(&self) -> &str {
        match self {
            Check::Present(field) | Check::Literals(field, _) | Check::Kind(field, _) => field,
        }
    }
}

/// `#1` is the number 1 at run time, `#01` the string "01".
fn is_hash_number(text: &str) -> bool {
    match text.as_bytes() {
        [b'0'..=b'9'] => true,
        [b'1'..=b'9', rest @ ..] => rest.iter().all(u8::is_ascii_digit) && text.parse::<i32>().is_ok(),
        _ => false,
    }
}

fn literal_kind(literal: &Literal) -> Option<&'static str> {
    match literal {
        Literal::Str(_) => Some("string"),
        Literal::Num(_) => Some("number"),
        Literal::Bool(_) => Some("boolean"),
        Literal::Other => None,
    }
}

fn literals_kind(literals: &[Literal]) -> Option<&'static str> {
    let first = literal_kind(literals.first()?)?;
    literals.iter().all(|literal| literal_kind(literal) == Some(first)).then_some(first)
}

/// What `typeof` answers for a kind.
fn typeof_of(kind: &str) -> Option<&'static str> {
    match kind {
        "string" => Some("string"),
        "number" => Some("number"),
        "bigint" => Some("bigint"),
        "boolean" => Some("boolean"),
        "symbol" => Some("symbol"),
        "function" => Some("function"),
        "object" | "array" | "instance" => Some("object"),
        _ => None,
    }
}

/// No value of the member passes the check. This mirrors the compiler
/// (`compiler-rust/src/types/variant_layout.rs`, `fails`).
fn check_fails(check: &Check, shape: &ObjectShape) -> bool {
    let ObjectShape::Closed(fields) = shape else {
        return true;
    };
    let Some(field) = fields.iter().find(|field| field.name == check.field()) else {
        return true;
    };
    match check {
        Check::Present(_) => false,
        Check::Literals(_, literals) => !literals.iter().any(|literal| {
            match (&field.literals, field.kind.and_then(typeof_of)) {
                (Some(own), _) => own.contains(literal),
                (None, Some(own)) => literal_kind(literal).is_none_or(|kind| typeof_of(kind) == Some(own)),
                (None, None) => true,
            }
        }),
        Check::Kind(_, "array") => field.kind.is_some_and(|kind| kind != "array"),
        Check::Kind(_, kind) => match (field.kind.and_then(typeof_of), typeof_of(kind)) {
            (Some(own), Some(checked)) => own != checked,
            _ => false,
        },
    }
}

/// The checks every value of a member passes: literal, then presence, then
/// kind, each in field order.
fn candidate_checks(shape: &ObjectShape) -> Vec<Check> {
    let ObjectShape::Closed(fields) = shape else {
        return Vec::new();
    };
    let required = || fields.iter().filter(|field| field.required);
    let literal = required()
        .filter_map(|field| field.literals.clone().map(|literals| Check::Literals(field.name.clone(), literals)));
    let presence = required().map(|field| Check::Present(field.name.clone()));
    let kind = required().filter_map(|field| match field.kind {
        Some(kind @ ("string" | "number" | "bigint" | "boolean" | "function" | "object" | "array")) => {
            Some(Check::Kind(field.name.clone(), kind))
        }
        _ => None,
    });
    literal.chain(presence).chain(kind).collect()
}

/// Whether `shape` has a test, one check or several joined with `&&`, that
/// every member of `others` fails.
fn has_test(shape: &ObjectShape, others: &[&ObjectShape]) -> bool {
    let mut uncovered: Vec<&ObjectShape> = others.to_vec();
    for check in candidate_checks(shape) {
        uncovered.retain(|other| !check_fails(&check, other));
        if uncovered.is_empty() {
            return true;
        }
    }
    false
}

/// Whether the compiler finds an order for these object members: it tests,
/// one at a time, a member with a test every other remaining member fails.
/// An open member has no test, so there is at most one, and it is last.
fn objects_ordered(mut remaining: Vec<ObjectShape>) -> bool {
    if remaining.iter().filter(|shape| matches!(shape, ObjectShape::Open)).count() > 1 {
        return false;
    }
    while remaining.len() > 1 {
        let found = (0..remaining.len()).find(|&index| {
            let others: Vec<&ObjectShape> =
                remaining.iter().enumerate().filter(|(other, _)| *other != index).map(|(_, shape)| shape).collect();
            has_test(&remaining[index], &others)
        });
        match found {
            Some(index) => {
                remaining.remove(index);
            }
            None => return false,
        }
    }
    true
}

/// `ty` with the type variables `params` replaced by `args`.
fn substitute(ty: &Ty, params: &[String], args: &[Ty]) -> Ty {
    match ty {
        Ty::Var(name) => match params.iter().position(|param| param == name) {
            Some(index) => args.get(index).cloned().unwrap_or_else(|| ty.clone()),
            None => ty.clone(),
        },
        Ty::App(name, items) => Ty::App(name.clone(), items.iter().map(|item| substitute(item, params, args)).collect()),
        Ty::Tuple(items) => Ty::Tuple(items.iter().map(|item| substitute(item, params, args)).collect()),
        Ty::Fn(fn_params, ret) => Ty::Fn(
            fn_params
                .iter()
                .map(|param| Param { ty: substitute(&param.ty, params, args), ..param.clone() })
                .collect(),
            Box::new(substitute(ret, params, args)),
        ),
        Ty::Poly(_) => ty.clone(),
    }
}

/// One member made of several: a field both have is required when both
/// require it and keeps the literals and kind they share; a field one of them
/// lacks is optional.
fn merge_shapes(a: &ObjectShape, b: &ObjectShape) -> ObjectShape {
    let (ObjectShape::Closed(a), ObjectShape::Closed(b)) = (a, b) else {
        return ObjectShape::Open;
    };
    let mut fields: Vec<FieldShape> = Vec::new();
    for field in a.iter().chain(b) {
        if fields.iter().any(|other| other.name == field.name) {
            continue;
        }
        let in_a = a.iter().find(|other| other.name == field.name);
        let in_b = b.iter().find(|other| other.name == field.name);
        fields.push(match (in_a, in_b) {
            (Some(x), Some(y)) if x.required && y.required => FieldShape {
                name: field.name.clone(),
                required: true,
                literals: match (&x.literals, &y.literals) {
                    (Some(l), Some(m)) => {
                        let mut all = l.clone();
                        all.extend(m.iter().filter(|literal| !l.contains(literal)).cloned());
                        Some(all)
                    }
                    _ => None,
                },
                kind: if x.kind == y.kind { x.kind } else { None },
            },
            _ => FieldShape { name: field.name.clone(), required: false, literals: None, kind: None },
        });
    }
    ObjectShape::Closed(fields)
}

/// The object members of a union in groups that become one case each:
/// members that no check tells apart, in either direction, are merged until
/// none are left, as no order could test either first. `None` when the
/// groups still have no order, or there is more than one open member.
fn object_groups(shapes: Vec<ObjectShape>) -> Option<Vec<Vec<usize>>> {
    if shapes.iter().filter(|shape| matches!(shape, ObjectShape::Open)).count() > 1 {
        return None;
    }
    let mut groups: Vec<(Vec<usize>, ObjectShape)> =
        shapes.into_iter().enumerate().map(|(index, shape)| (vec![index], shape)).collect();
    // A merged member can only become harder to tell apart from the others,
    // so one pass that retries the pairs of each merged member is enough.
    let mut i = 0;
    while i < groups.len() {
        let mut j = i + 1;
        let mut merged = false;
        while j < groups.len() {
            let (a, b) = (&groups[i].1, &groups[j].1);
            if !matches!(a, ObjectShape::Open)
                && !matches!(b, ObjectShape::Open)
                && !has_test(a, &[b])
                && !has_test(b, &[a])
            {
                let (indices, shape) = groups.remove(j);
                groups[i].1 = merge_shapes(&groups[i].1, &shape);
                groups[i].0.extend(indices);
                merged = true;
            } else {
                j += 1;
            }
        }
        // The merged member is compared with the earlier ones again.
        if merged && i > 0 {
            i = 0;
        } else {
            i += 1;
        }
    }
    objects_ordered(groups.iter().map(|(_, shape)| shape.clone()).collect())
        .then(|| groups.into_iter().map(|(indices, _)| indices).collect())
}
