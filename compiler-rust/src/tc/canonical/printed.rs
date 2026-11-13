//! The `== printed` section: the signature as `Printtyp` prints it for a
//! user (compiler-rust/src/types/printtyp.rs `tree_of_modtype_in_unit`, then
//! `print_out_module_type`), from segment rows.
//!
//! The outcome tree is not materialized: each outcome node becomes its
//! document as soon as its children are done, carrying the one fact about
//! its shape a parent's layout reads ([`Kind`]). Names are given in the
//! order `Printtyp` gives them, because every walk visits nodes in the
//! order the recursive original does: types, loop marks, signatures and
//! module types all run on explicit stacks.

use super::doc::{D, Docs};
use super::normalize::{ObjectField, is_row_name};
use super::view::{Desc, Graph, Marks, N, Slots};
use crate::fast_hash::AHashMap;
use crate::tc::graph::{GENERIC, NONE};
use crate::tc::segment::{
    AttributePayloadRow, DeclarationKind, ExtensionStatus, ExternalKindRow, FfiRow,
    InlineConstantRow, ItemStatus, LiteralRow, LongidentRow, ModuleSourceRow, ModuleTypeRow,
    PathRow, PrimitiveKindRow, Range, RecStatus, ReturnWrapperRow, RowFieldKind,
    RuntimeConstructorRow, SemanticStringValue, SignatureKind,
};

/// predef.rs `STAMP_OPTION`: `Predef.path_option` is `Pident` of the
/// identifier with this stamp (compiler-rust/src/types/predef.rs:26).
const OPTION_STAMP: i32 = 11;

/// What a parent's layout reads of an outcome type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Other,
    Tuple,
    Arrow,
    Record,
    /// `Otyp_var`, with its name.
    Var(u32),
}

/// One finished outcome type. Eight bytes.
#[derive(Clone, Copy, Debug)]
struct Out {
    doc: D,
    kind: Kind,
}

/// Flags of a variant's outcome.
const CLOSED: u8 = 1;
const ALL_PRESENT: u8 = 2;
const NON_GEN: u8 = 4;

/// One variant field of `Ovar_fields`: its tag, its `&` and type count.
#[derive(Clone, Copy)]
struct VField {
    label: u32,
    count: u32,
    ampersand: bool,
}

/// One object field: name and mutability.
#[derive(Clone, Copy)]
struct OField {
    name: u32,
    mutable: bool,
}

/// `tree_of_typexp` work. At most sixteen bytes.
#[derive(Clone, Copy)]
enum Task {
    Enter {
        ty: N,
        sch: bool,
    },
    /// A finished outcome known before its turn: keeps results in order.
    Push(Out),
    Alias {
        px: N,
    },
    Arrow {
        params: Slots,
    },
    Tuple {
        len: u32,
    },
    Record {
        labels: Range,
    },
    Constr {
        ident: D,
        len: u32,
    },
    VariantNamed {
        ident: D,
        len: u32,
        flags: u8,
    },
    VariantFields {
        fields: Range,
        flags: u8,
    },
    Object {
        fields: Range,
        rest: u8,
    },
    /// Pops a [`PolyFrame`].
    Poly,
    /// `docs[0]` is the path's name; the rest the constraint names.
    Module {
        docs: Range,
        args: u32,
    },
}

/// A `Tpoly` whose body is being printed.
#[derive(Clone, Copy)]
struct PolyFrame {
    vars: Slots,
    names: Range,
    delayed_mark: u32,
}

/// What a module type became. Twelve bytes.
#[derive(Clone, Copy)]
enum Mty {
    /// A document printed as is (an identifier).
    Plain(D),
    /// An alias: the identifier, printed only by a module item.
    Alias(D),
    /// `Omty_signature []`.
    EmptySignature,
    Signature(D),
    /// A functor: the head of its `functor_params` list and its final result.
    Functor {
        params: u32,
        result: D,
    },
}

/// One functor parameter of a collected chain: name, type, next (NONE: last).
#[derive(Clone, Copy)]
struct FunctorParam {
    name: u32,
    next: u32,
    arg: Option<D>,
}

/// One printed signature item. Twelve bytes.
#[derive(Clone, Copy)]
enum SigOut {
    Doc(D),
    /// An extension constructor: its constructor document and its
    /// `type name<params>` header.
    Ext {
        constructor: D,
        header: D,
        status: u8,
        private: bool,
    },
}

/// Signature walk work. At most sixteen bytes.
#[derive(Clone, Copy)]
enum Step {
    /// The next item of the innermost signature frame.
    Next,
    Mty {
        row: u32,
        ellipsis: bool,
    },
    /// Finish a module item.
    Module {
        name: u32,
        status: u8,
        scoped: bool,
    },
    /// Finish a module type item.
    ModuleTypeDecl {
        name: u32,
    },
    /// Finish a functor.
    Functor {
        param: u32,
        has_type: bool,
    },
}

/// A signature being printed (`tree_of_signature`).
struct SigFrame {
    next: u32,
    end: u32,
    saved_visible: u32,
    hidden_start: u32,
    items_start: u32,
    in_group: bool,
}

/// Names (`names`, `name_counter`, `named_vars`, the weak tables) with
/// dense per-node and per-name tables. Name texts are interned once.
#[derive(Default)]
struct Names {
    texts: Vec<String>,
    ids: AHashMap<String, u32>,
    /// Per node: (epoch, name) of `names`.
    of: Vec<(u32, u32)>,
    epoch: u32,
    list: Vec<(N, u32)>,
    /// Per name: occurrences in `list`.
    count: Vec<u32>,
    counter: usize,
    named_vars: Vec<bool>,
    named_var_list: Vec<u32>,
    weak_counter: usize,
    /// Per node: its weak name, never reset.
    weak_of: Vec<u32>,
    weak_used: Vec<bool>,
}

impl Names {
    /// Amortized O(length): the id of a name text.
    fn intern(&mut self, text: &str) -> u32 {
        if let Some(&id) = self.ids.get(text) {
            return id;
        }
        let id = self.texts.len() as u32;
        self.texts.push(text.to_string());
        self.ids.insert(text.to_string(), id);
        self.count.push(0);
        self.named_vars.push(false);
        self.weak_used.push(false);
        id
    }

    /// O(1).
    fn get(&self, n: N) -> Option<u32> {
        match self.of.get(n.0 as usize) {
            Some(&(epoch, name)) if epoch == self.epoch && self.epoch != 0 => Some(name),
            _ => None,
        }
    }

    /// Amortized O(1).
    fn insert(&mut self, n: N, name: u32) {
        if self.epoch == 0 {
            self.epoch = 1;
        }
        let index = n.0 as usize;
        if index >= self.of.len() {
            self.of.resize((index + 1).next_power_of_two(), (0, 0));
        }
        self.of[index] = (self.epoch, name);
        self.list.push((n, name));
        self.count[name as usize] += 1;
    }

    /// O(names): `remove_names` of one node.
    fn remove(&mut self, n: N) {
        if let Some(name) = self.get(n) {
            self.of[n.0 as usize].0 = 0;
            self.count[name as usize] -= 1;
            self.list.retain(|(m, _)| *m != n);
        }
    }

    /// O(names): `reset_names`.
    fn reset(&mut self) {
        self.clear_list();
        self.counter = 0;
        for name in self.named_var_list.drain(..) {
            self.named_vars[name as usize] = false;
        }
    }

    /// O(names).
    fn clear_list(&mut self) {
        for (_, name) in self.list.drain(..) {
            self.count[name as usize] = 0;
        }
        self.epoch = self.epoch.checked_add(1).expect("name epoch exhausted");
    }

    /// O(names): `std::mem::take (names)`.
    fn take(&mut self) -> Vec<(N, u32)> {
        let saved = self.list.clone();
        self.clear_list();
        saved
    }

    /// O(names): restore what [`Self::take`] returned.
    fn restore(&mut self, saved: Vec<(N, u32)>) {
        self.clear_list();
        for (n, name) in saved {
            self.insert(n, name);
        }
    }

    /// O(1): `name_is_already_used`.
    fn used(&self, name: u32) -> bool {
        self.named_vars[name as usize]
            || self.count[name as usize] > 0
            || self.weak_used[name as usize]
    }
}

pub(super) struct Printed<'g, 's> {
    g: &'g mut Graph<'s>,
    docs: Docs,
    names: Names,
    visited_objects: Marks,
    aliased: Marks,
    delayed: Marks,
    delayed_log: Vec<(N, bool)>,
    /// `mark_loops`'s path: per node, how often it is on the current path.
    on_path: Vec<u32>,
    /// Names of the signature's types added so far (`signature_types`),
    /// a string per entry; the first `visible` are in scope.
    signature_types: Vec<u32>,
    visible: u32,
    hidden: Vec<u32>,
    /// The current declaration's inlined records (`printing_context`).
    inlined: Option<Range>,
    /// Module names of the persistent-unit prefixes below the unit.
    prefixes: Vec<u32>,
    unit_name: u32,
    // Pools of the walks, reused.
    tasks: Vec<Task>,
    results: Vec<Out>,
    polys: Vec<PolyFrame>,
    vfields: Vec<VField>,
    ofields: Vec<OField>,
    dpool: Vec<D>,
    name_pool: Vec<u32>,
    params: Vec<N>,
    fields: Vec<ObjectField>,
    free: Vec<N>,
    free_marks: Marks,
    scratch: String,
    functor_params: Vec<FunctorParam>,
    mtys: Vec<Mty>,
    frames: Vec<SigFrame>,
    items: Vec<SigOut>,
}

impl<'g, 's> Printed<'g, 's> {
    pub fn new(g: &'g mut Graph<'s>) -> Self {
        let unit_name = g.v.p.unit.map_or(NONE, |unit| unit.name);
        Printed {
            g,
            docs: Docs::default(),
            names: Names {
                weak_counter: 1,
                ..Names::default()
            },
            visited_objects: Marks::default(),
            aliased: Marks::default(),
            delayed: Marks::default(),
            delayed_log: Vec::new(),
            on_path: Vec::new(),
            signature_types: Vec::new(),
            visible: 0,
            hidden: Vec::new(),
            inlined: None,
            prefixes: Vec::new(),
            unit_name,
            tasks: Vec::new(),
            results: Vec::new(),
            polys: Vec::new(),
            vfields: Vec::new(),
            ofields: Vec::new(),
            dpool: Vec::new(),
            name_pool: Vec::new(),
            params: Vec::new(),
            fields: Vec::new(),
            free: Vec::new(),
            free_marks: Marks::default(),
            scratch: String::new(),
            functor_params: Vec::new(),
            mtys: Vec::new(),
            frames: Vec::new(),
            items: Vec::new(),
        }
    }

    // ------------------------------------------------------------------
    // Text helpers
    // ------------------------------------------------------------------

    fn text(&mut self, text: &str) -> D {
        self.docs.text(text)
    }

    /// O(text): `print_ident_like txt allow_uident false` as text.
    fn ident_like(out: &mut String, text: &str, allow_uident: bool) {
        match crate::parser::printer::print_ident_like(text, allow_uident, false) {
            crate::parser::doc::Doc::Text(text) => out.push_str(&text),
            doc => out.push_str(&doc.to_string(80)),
        }
    }

    /// O(text): `print_string_literal_doc`.
    fn string_literal(out: &mut String, text: &str) {
        out.push('"');
        out.push_str(&crate::string_literal::encode_js_string(text));
        out.push('"');
    }

    fn str(&self, index: u32) -> &'s str {
        self.g.v.str(index)
    }

    // ------------------------------------------------------------------
    // Paths
    // ------------------------------------------------------------------

    /// O(path length): `Path.name ()`, with the last name trimmed of `#row`.
    fn path_name(&self, out: &mut String, path: u32, trim: bool) {
        #[derive(Clone, Copy)]
        enum P {
            Path(u32, bool),
            Name(u32, bool),
            Char(u8),
        }
        let mut work: smallvec::SmallVec<[P; 8]> = smallvec::smallvec![P::Path(path, trim)];
        let v = &self.g.v;
        while let Some(step) = work.pop() {
            match step {
                P::Char(c) => out.push(c as char),
                P::Name(name, trim) => out.push_str(trim_row(v.str(name), trim)),
                P::Path(p, trim) => match v.path(p) {
                    PathRow::Ident(id) => out.push_str(trim_row(v.str(v.ident(id).name), trim)),
                    PathRow::Dot { parent, name, .. } => {
                        work.push(P::Name(name, trim));
                        work.push(P::Char(b'.'));
                        work.push(P::Path(parent, false));
                    }
                    PathRow::Apply { functor, argument } => {
                        work.push(P::Char(b')'));
                        work.push(P::Path(argument, false));
                        work.push(P::Char(b'('));
                        work.push(P::Path(functor, false));
                    }
                },
            }
        }
    }

    /// O(path length): the names of a `Pdot` chain rooted at the unit, from
    /// the unit, into `out`; false for any other path.
    fn unit_spine(&self, path: u32, out: &mut smallvec::SmallVec<[u32; 8]>) -> bool {
        out.clear();
        let mut current = path;
        loop {
            match self.g.v.path(current) {
                PathRow::Ident(id) => {
                    let row = self.g.v.ident(id);
                    out.reverse();
                    return row.stamp == 0 && row.name == self.unit_name;
                }
                PathRow::Dot { parent, name, .. } => {
                    out.push(name);
                    current = parent;
                }
                PathRow::Apply { .. } => return false,
            }
        }
    }

    /// O(visible signature types): `non_shadowed_pervasive_or_stdlib` with
    /// `Env.empty` as the printing environment.
    fn non_shadowed_pervasive(&self, path: u32, trim: bool) -> bool {
        let v = &self.g.v;
        let PathRow::Dot { parent, name, .. } = v.path(path) else {
            return false;
        };
        let PathRow::Ident(id) = v.path(parent) else {
            return false;
        };
        let row = v.ident(id);
        if !(row.stamp == 0 && matches!(v.str(row.name), "Pervasives" | "Stdlib")) {
            return false;
        }
        let s = trim_row(v.str(name), trim);
        // A visible signature type of that name is `Pident`, never `same`
        // as this `Pdot`.
        !self.signature_types[..self.visible as usize]
            .iter()
            .any(|&ty| v.str(ty) == s)
    }

    /// O(path length + output), explicit stack: `tree_of_path` printed by
    /// `print_out_ident_doc allow_uident`.
    fn ident_text(&self, out: &mut String, path: u32, trim: bool, allow_uident: bool) {
        #[derive(Clone, Copy)]
        enum P {
            Path(u32, bool, bool),
            Name(u32, bool),
            Char(u8),
        }
        let mut work: smallvec::SmallVec<[P; 8]> =
            smallvec::smallvec![P::Path(path, trim, allow_uident)];
        let mut spine = smallvec::SmallVec::<[u32; 8]>::new();
        let mut name = String::new();
        let v = &self.g.v;
        while let Some(step) = work.pop() {
            match step {
                P::Char(c) => out.push(c as char),
                P::Name(text, trim) => out.push_str(trim_row(v.str(text), trim)),
                P::Path(p, trim, allow) => {
                    // `unit_relative_path`: the longest prefix leaving a name.
                    if self.unit_spine(p, &mut spine) && !spine.is_empty() {
                        let common = spine
                            .iter()
                            .zip(self.prefixes.iter())
                            .take_while(|(a, b)| a == b)
                            .count();
                        let from = common.min(spine.len() - 1);
                        let last = spine.len() - 1;
                        // A dotted identifier prints its first part with
                        // `allow_uident` (`print_out_ident_doc true`).
                        let allow_first = allow || from < last;
                        for (k, part) in spine[from..].iter().enumerate() {
                            let text = trim_row(v.str(*part), trim && from + k == last);
                            if k == 0 {
                                Self::ident_like(out, text, allow_first);
                            } else {
                                out.push('.');
                                out.push_str(text);
                            }
                        }
                        continue;
                    }
                    match v.path(p) {
                        PathRow::Ident(id) => {
                            Self::ident_like(out, trim_row(v.str(v.ident(id).name), trim), allow)
                        }
                        PathRow::Dot { name: s, .. } if self.non_shadowed_pervasive(p, trim) => {
                            Self::ident_like(out, trim_row(v.str(s), trim), allow)
                        }
                        PathRow::Dot {
                            parent, name: s, ..
                        } => {
                            name.clear();
                            self.path_name(&mut name, parent, false);
                            if let Some(rest) = name.strip_prefix("Stdlib_") {
                                Self::ident_like(out, rest, true);
                                out.push('.');
                                out.push_str(trim_row(v.str(s), trim));
                            } else {
                                work.push(P::Name(s, trim));
                                work.push(P::Char(b'.'));
                                work.push(P::Path(parent, false, true));
                            }
                        }
                        PathRow::Apply { functor, argument } => {
                            work.push(P::Char(b')'));
                            work.push(P::Path(argument, false, true));
                            work.push(P::Char(b'('));
                            work.push(P::Path(functor, false, true));
                        }
                    }
                }
            }
        }
    }

    /// O(path): the identifier document.
    fn ident_doc(&mut self, path: u32, trim: bool, allow_uident: bool) -> D {
        let mut text = std::mem::take(&mut self.scratch);
        text.clear();
        self.ident_text(&mut text, path, trim, allow_uident);
        let doc = self.docs.text(&text);
        self.scratch = text;
        doc
    }

    /// O(1): whether a path is `Predef.path_option`.
    fn is_option(&self, path: u32, trim: bool) -> bool {
        !trim
            && matches!(self.g.v.path(path), PathRow::Ident(id)
                if self.g.v.ident(id).stamp == OPTION_STAMP)
    }

    // ------------------------------------------------------------------
    // Names and loop marks
    // ------------------------------------------------------------------

    /// O(names): `reset`.
    fn reset(&mut self) {
        self.names.reset();
        self.visited_objects.clear();
        self.aliased.clear();
        self.delayed.clear();
        self.delayed_log.clear();
    }

    /// O(1): the given name of a variable, NONE otherwise.
    fn given_name(&self, n: N) -> u32 {
        match self.g.desc(n) {
            Desc::Var(name) | Desc::Univar(name) => name,
            _ => NONE,
        }
    }

    /// O(name): `add_named_var`.
    fn add_named_var(&mut self, n: N) {
        let given = self.given_name(n);
        if given != NONE {
            let id = self.names.intern(self.g.v.str(given));
            if !self.names.named_vars[id as usize] {
                self.names.named_vars[id as usize] = true;
                self.names.named_var_list.push(id);
            }
        }
    }

    /// O(fields): `is_aliased`.
    fn is_aliased(&mut self, n: N) -> bool {
        let px = self.g.proxy(n);
        self.aliased.has(px)
    }

    /// O(fields): `add_alias`.
    fn add_alias(&mut self, n: N) {
        let px = self.g.proxy(n);
        if !self.is_aliased(px) {
            self.aliased.insert(px);
            self.add_named_var(px);
        }
    }

    /// O(1): `aliasable`.
    fn aliasable(&self, n: N) -> bool {
        !matches!(
            self.g.desc(n),
            Desc::Var(_) | Desc::Univar(_) | Desc::Poly { .. }
        )
    }

    /// O(1): `is_non_gen`.
    fn is_non_gen(&self, sch: bool, n: N) -> bool {
        sch && matches!(self.g.desc(n), Desc::Var(_)) && self.g.level(n) != GENERIC
    }

    /// O(1) amortized.
    fn add_delayed(&mut self, n: N) {
        if !self.delayed.has(n) {
            self.delayed.insert(n);
            self.delayed_log.push((n, false));
        }
    }

    /// O(1) amortized.
    fn remove_delayed(&mut self, n: N) {
        if self.delayed.has(n) {
            self.delayed.remove(n);
            self.delayed_log.push((n, true));
        }
    }

    /// O(changes since `mark`): restore a saved `delayed`.
    fn restore_delayed(&mut self, mark: u32) {
        while self.delayed_log.len() as u32 > mark {
            let (n, present) = self.delayed_log.pop().expect("a delayed change");
            if present {
                self.delayed.insert(n);
            } else {
                self.delayed.remove(n);
            }
        }
    }

    /// Amortized O(candidates): `new_name`.
    fn new_name(&mut self) -> u32 {
        loop {
            let letter = (b'a' + (self.names.counter % 26) as u8) as char;
            let text = if self.names.counter < 26 {
                letter.to_string()
            } else {
                format!("{letter}{}", self.names.counter / 26)
            };
            self.names.counter += 1;
            let id = self.names.intern(&text);
            if !self.names.used(id) {
                return id;
            }
        }
    }

    /// Amortized O(candidates): `new_weak_name`.
    fn new_weak_name(&mut self, n: N) -> u32 {
        loop {
            let text = format!("weak{}", self.names.weak_counter);
            self.names.weak_counter += 1;
            let id = self.names.intern(&text);
            if !self.names.used(id) {
                self.names.weak_used[id as usize] = true;
                let index = n.0 as usize;
                if index >= self.names.weak_of.len() {
                    self.names
                        .weak_of
                        .resize((index + 1).next_power_of_two(), NONE);
                }
                self.names.weak_of[index] = id;
                return id;
            }
        }
    }

    /// Amortized O(candidates): `name_of_type`.
    fn name_of_type(&mut self, weak: bool, t: N) -> u32 {
        if let Some(name) = self.names.get(t) {
            return name;
        }
        if let Some(&name) = self.names.weak_of.get(t.0 as usize)
            && name != NONE
        {
            return name;
        }
        let given = self.given_name(t);
        let name = if given != NONE {
            let base = self.g.v.str(given);
            let mut current = self.names.intern(base);
            let mut i = 0;
            while self.names.count[current as usize] > 0 {
                current = self.names.intern(&format!("{base}{i}"));
                i += 1;
            }
            current
        } else if weak {
            self.new_weak_name(t)
        } else {
            self.new_name()
        };
        if self.names.texts[name as usize] != "_" {
            self.names.insert(t, name);
        }
        name
    }

    /// O(path + fields): the `mark_loops` of one root, after normalizing it.
    fn mark_loops(&mut self, root: N) {
        self.g.normalize(root);
        #[derive(Clone, Copy)]
        enum M {
            Enter(N),
            Exit(N),
        }
        let mut work = vec![M::Enter(root)];
        let mut children: smallvec::SmallVec<[N; 8]> = smallvec::SmallVec::new();
        let mut fields = std::mem::take(&mut self.fields);
        while let Some(step) = work.pop() {
            #[cfg(test)]
            crate::tc::steps::tick();
            let ty = match step {
                M::Exit(px) => {
                    self.on_path[px.0 as usize] -= 1;
                    continue;
                }
                M::Enter(ty) => ty,
            };
            let px = self.g.proxy(ty);
            let on_path = self
                .on_path
                .get(px.0 as usize)
                .is_some_and(|count| *count > 0);
            if on_path && self.aliasable(ty) {
                self.add_alias(px);
                continue;
            }
            if px.0 as usize >= self.on_path.len() {
                self.on_path
                    .resize((px.0 as usize + 1).next_power_of_two(), 0);
            }
            self.on_path[px.0 as usize] += 1;
            work.push(M::Exit(px));
            children.clear();
            match self.g.desc(ty) {
                Desc::Var(_) | Desc::Univar(_) => self.add_named_var(ty),
                Desc::Arrow { params, ret } => {
                    for i in 0..params.len {
                        children.push(self.g.param(params, i).1);
                    }
                    children.push(ret);
                }
                Desc::Tuple(slots)
                | Desc::Constr { args: slots, .. }
                | Desc::Package { args: slots, .. } => {
                    for i in 0..slots.len {
                        children.push(self.g.slot(slots, i));
                    }
                }
                Desc::Variant => {
                    if self.visited_objects.has(px) {
                        self.add_alias(px);
                    } else {
                        let row = self.g.row(ty);
                        if !self.g.static_row(ty) {
                            self.visited_objects.insert(px);
                        }
                        if row.name != NONE && self.namable_row(ty) {
                            for i in 0..row.name_args.len {
                                children.push(self.g.ns_at(row.name_args, i));
                            }
                        } else {
                            // `iter_row`: the fields' types, then the name's
                            // arguments when `more` is not a row.
                            self.g.row_types(row, &mut children);
                            if matches!(
                                self.g.desc(row.more),
                                Desc::Var(_)
                                    | Desc::Univar(_)
                                    | Desc::Subst(_)
                                    | Desc::Constr { .. }
                                    | Desc::Nil
                            ) {
                                for i in 0..row.name_args.len {
                                    children.push(self.g.ns_at(row.name_args, i));
                                }
                            }
                        }
                    }
                }
                Desc::Object(head) => {
                    if self.visited_objects.has(px) {
                        self.add_alias(px);
                    } else {
                        if self.opened_object(head) {
                            self.visited_objects.insert(px);
                        }
                        self.g.flatten_fields(head, &mut fields);
                        children.extend(fields.iter().map(|field| field.typ));
                    }
                }
                Desc::Field { typ, rest, .. } => {
                    children.push(typ);
                    children.push(rest);
                }
                Desc::Nil => {}
                Desc::Subst(target) => children.push(target),
                Desc::Poly { body, vars } => {
                    for i in 0..vars.len {
                        let var = self.g.slot(vars, i);
                        self.add_alias(var);
                    }
                    children.push(body);
                }
            }
            work.extend(children.iter().rev().map(|&child| M::Enter(child)));
        }
        self.fields = fields;
    }

    /// O(fields): `opened_object` of an object's field chain.
    fn opened_object(&self, head: N) -> bool {
        let mut current = head;
        loop {
            match self.g.desc(current) {
                Desc::Field { rest, .. } => current = rest,
                Desc::Var(_) | Desc::Univar(_) | Desc::Constr { .. } => return true,
                _ => return false,
            }
        }
    }

    /// O(fields): `namable_row`.
    fn namable_row(&mut self, ty: N) -> bool {
        let row = self.g.row(ty);
        row.name != NONE
            && (0..row.fields.len).all(|i| {
                let field = self.g.field(row.fields, i);
                match field.kind {
                    RowFieldKind::Either { constant, .. } => {
                        row.closed
                            && if constant {
                                field.types.len == 0
                            } else {
                                field.types.len == 1
                            }
                    }
                    _ => true,
                }
            })
    }

    // ------------------------------------------------------------------
    // tree_of_typexp
    // ------------------------------------------------------------------

    /// O(nodes printed, with sharing re-expanded as the original does):
    /// `tree_of_typexp sch ty` laid out as `print_out_type_doc`.
    fn tree(&mut self, sch: bool, ty: N) -> Out {
        let base = self.tasks.len();
        let results = self.results.len();
        self.tasks.push(Task::Enter { ty, sch });
        while self.tasks.len() > base {
            #[cfg(test)]
            crate::tc::steps::tick();
            let task = self.tasks.pop().expect("a task");
            match task {
                Task::Enter { ty, sch } => self.enter(ty, sch),
                Task::Push(out) => self.results.push(out),
                Task::Alias { px } => {
                    let inner = self.results.pop().expect("an aliased type");
                    let name = self.name_of_type(false, px);
                    let open = self.text("(");
                    let text = format!(" as '{}", self.names.texts[name as usize]);
                    let as_ = self.text(&text);
                    let close = self.text(")");
                    let doc = self.docs.concat(&[open, inner.doc, as_, close]);
                    self.results.push(Out {
                        doc,
                        kind: Kind::Other,
                    });
                }
                Task::Arrow { params } => self.build_arrow(params),
                Task::Tuple { len } => {
                    let start = self.results.len() - len as usize;
                    let docs: smallvec::SmallVec<[D; 8]> =
                        self.results[start..].iter().map(|out| out.doc).collect();
                    self.results.truncate(start);
                    let doc = self.list_doc("(", &docs, ")");
                    self.results.push(Out {
                        doc,
                        kind: Kind::Tuple,
                    });
                }
                Task::Record { labels } => {
                    let doc = self.record_rows(labels, true);
                    self.results.push(Out {
                        doc,
                        kind: Kind::Record,
                    });
                }
                Task::Constr { ident, len } => {
                    let doc = self.constr_doc(ident, len);
                    self.results.push(Out {
                        doc,
                        kind: Kind::Other,
                    });
                }
                Task::VariantNamed { ident, len, flags } => {
                    let inner = self.constr_doc(ident, len);
                    let doc = if flags & CLOSED != 0 && flags & ALL_PRESENT != 0 {
                        inner
                    } else {
                        self.variant_doc(flags, inner)
                    };
                    self.results.push(Out {
                        doc,
                        kind: Kind::Other,
                    });
                }
                Task::VariantFields { fields, flags } => {
                    let body = self.variant_fields_doc(fields);
                    let doc = self.variant_doc(flags, body);
                    self.results.push(Out {
                        doc,
                        kind: Kind::Other,
                    });
                }
                Task::Object { fields, rest } => {
                    let doc = self.object_doc(fields, rest);
                    self.results.push(Out {
                        doc,
                        kind: Kind::Other,
                    });
                }
                Task::Poly => {
                    let frame = self.polys.pop().expect("a poly frame");
                    let body = self.results.pop().expect("a poly body");
                    let mut parts: smallvec::SmallVec<[D; 8]> = smallvec::SmallVec::new();
                    for i in 0..frame.names.len {
                        let name = self.name_pool[(frame.names.start + i) as usize];
                        let text = format!("'{}", self.names.texts[name as usize]);
                        parts.push(self.docs.text(&text));
                    }
                    let space = self.text(" ");
                    let vars = self.docs.join(space, &parts);
                    let dot = self.text(".");
                    let space = self.text(" ");
                    let all = self.docs.concat(&[vars, dot, space, body.doc]);
                    let doc = self.docs.group(all);
                    for i in 0..frame.vars.len {
                        let var = self.g.slot(frame.vars, i);
                        self.names.remove(var);
                    }
                    self.restore_delayed(frame.delayed_mark);
                    self.results.push(Out {
                        doc,
                        kind: Kind::Other,
                    });
                }
                Task::Module { docs, args } => {
                    let doc = self.module_doc(docs, args);
                    self.results.push(Out {
                        doc,
                        kind: Kind::Other,
                    });
                }
            }
        }
        debug_assert_eq!(self.results.len(), results + 1);
        self.results.pop().expect("a printed type")
    }

    /// Queue `tasks` to run in order.
    fn queue(&mut self, tasks: &[Task]) {
        self.tasks.extend(tasks.iter().rev());
    }

    /// O(1) plus the node's immediate fields: the prologue of
    /// `tree_of_typexp` and the dispatch of `pr_typ`.
    fn enter(&mut self, ty: N, sch: bool) {
        let px = self.g.proxy(ty);
        if self.names.get(px).is_some() && !self.delayed.has(px) {
            let mark = self.is_non_gen(sch, ty);
            let name = self.name_of_type(mark, px);
            let doc = self.var_doc(mark, name);
            self.results.push(Out {
                doc,
                kind: Kind::Var(name),
            });
            return;
        }
        let aliased = self.is_aliased(px) && self.aliasable(ty);
        self.remove_delayed(px);
        if aliased {
            self.name_of_type(false, px);
            self.tasks.push(Task::Alias { px });
        }
        match self.g.desc(ty) {
            Desc::Var(_) => {
                let non_gen = self.is_non_gen(sch, ty);
                let name = self.name_of_type(non_gen, ty);
                let doc = self.var_doc(non_gen, name);
                self.results.push(Out {
                    doc,
                    kind: Kind::Var(name),
                });
            }
            Desc::Univar(_) => {
                let name = self.name_of_type(false, ty);
                let doc = self.var_doc(false, name);
                self.results.push(Out {
                    doc,
                    kind: Kind::Var(name),
                });
            }
            Desc::Arrow { params, ret } => {
                let mut tasks: smallvec::SmallVec<[Task; 8]> = smallvec::SmallVec::new();
                for i in 0..params.len {
                    let (label, arg) = self.g.param(params, i);
                    if label != NONE && label & 1 != 0 {
                        let inner = match self.g.desc(arg) {
                            Desc::Constr { path, trim, args }
                                if args.len == 1 && self.is_option(path, trim) =>
                            {
                                Some(self.g.slot(args, 0))
                            }
                            _ => None,
                        };
                        tasks.push(match inner {
                            Some(inner) => Task::Enter { ty: inner, sch },
                            None => {
                                let doc = self.text("<hidden>");
                                Task::Push(Out {
                                    doc,
                                    kind: Kind::Other,
                                })
                            }
                        });
                    } else {
                        tasks.push(Task::Enter { ty: arg, sch });
                    }
                }
                tasks.push(Task::Enter { ty: ret, sch });
                tasks.push(Task::Arrow { params });
                self.queue(&tasks);
            }
            Desc::Tuple(slots) => {
                self.tasks.push(Task::Tuple { len: slots.len });
                for i in (0..slots.len).rev() {
                    let child = self.g.slot(slots, i);
                    self.tasks.push(Task::Enter { ty: child, sch });
                }
            }
            Desc::Constr { path, trim, args } => {
                if let Some(labels) = self.find_inlined(path, trim) {
                    self.tasks.push(Task::Record { labels });
                    self.queue_labels(labels);
                } else {
                    let ident = self.ident_doc(path, trim, args.len != 0);
                    self.tasks.push(Task::Constr {
                        ident,
                        len: args.len,
                    });
                    for i in (0..args.len).rev() {
                        let child = self.g.slot(args, i);
                        self.tasks.push(Task::Enter { ty: child, sch });
                    }
                }
            }
            Desc::Variant => self.enter_variant(sch, ty, px),
            Desc::Object(head) => self.enter_object(sch, head),
            Desc::Nil | Desc::Field { .. } => self.enter_object(sch, ty),
            Desc::Subst(target) => self.tasks.push(Task::Enter { ty: target, sch }),
            Desc::Poly { body, vars } => {
                if vars.len == 0 {
                    self.tasks.push(Task::Enter { ty: body, sch });
                } else {
                    let delayed_mark = self.delayed_log.len() as u32;
                    for i in 0..vars.len {
                        let var = self.g.slot(vars, i);
                        self.add_delayed(var);
                    }
                    let start = self.name_pool.len() as u32;
                    for i in 0..vars.len {
                        let var = self.g.slot(vars, i);
                        let name = self.name_of_type(false, var);
                        self.name_pool.push(name);
                    }
                    self.polys.push(PolyFrame {
                        vars,
                        names: Range {
                            start,
                            len: vars.len,
                        },
                        delayed_mark,
                    });
                    self.tasks.push(Task::Poly);
                    self.tasks.push(Task::Enter { ty: body, sch });
                }
            }
            Desc::Package { row, args } => {
                let package = self.g.v.p.packages[row as usize];
                let start = self.dpool.len() as u32;
                let mut name = std::mem::take(&mut self.scratch);
                name.clear();
                self.path_name(&mut name, package.path, false);
                let head = self.docs.text(&name);
                self.dpool.push(head);
                for i in 0..package.longidents.len {
                    let lid = self.g.v.p.indices[(package.longidents.start + i) as usize];
                    name.clear();
                    self.flatten_longident(&mut name, lid);
                    let doc = self.docs.text(&name);
                    self.dpool.push(doc);
                }
                self.scratch = name;
                self.tasks.push(Task::Module {
                    docs: Range {
                        start,
                        len: package.longidents.len + 1,
                    },
                    args: args.len,
                });
                for i in (0..args.len).rev() {
                    let child = self.g.slot(args, i);
                    self.tasks.push(Task::Enter { ty: child, sch });
                }
            }
        }
    }

    /// O(inlined records): `find_inlined_type (Path.name path)`.
    fn find_inlined(&mut self, path: u32, trim: bool) -> Option<Range> {
        let inlined = self.inlined?;
        let mut name = std::mem::take(&mut self.scratch);
        name.clear();
        self.path_name(&mut name, path, trim);
        let found = (0..inlined.len)
            .map(|i| self.g.v.p.inlined_records[(inlined.start + i) as usize])
            .find(|record| self.g.v.str(record.name) == name)
            .map(|record| record.labels);
        self.scratch = name;
        found
    }

    /// Queue the label types of `tree_of_label`, in order.
    fn queue_labels(&mut self, labels: Range) {
        for i in (0..labels.len).rev() {
            let label = self.g.v.p.labels[(labels.start + i) as usize];
            let ty = self.label_type(label.ty, label.optional);
            self.tasks.push(Task::Enter { ty, sch: false });
        }
    }

    /// O(1): `tree_of_label`'s type: an optional label's `option` argument.
    fn label_type(&self, root: u32, optional: bool) -> N {
        let ty = self.g.v.root_at(root);
        match self.g.desc(ty) {
            Desc::Constr { path, trim, args }
                if optional && args.len == 1 && self.is_option(path, trim) =>
            {
                self.g.slot(args, 0)
            }
            _ => ty,
        }
    }

    /// O(fields): `tree_of_variant`.
    fn enter_variant(&mut self, sch: bool, ty: N, px: N) {
        let row = self.g.row(ty);
        let mut shown = 0u32;
        let mut present = 0u32;
        for i in 0..row.fields.len {
            let field = self.g.field(row.fields, i);
            if !row.closed || field.kind != RowFieldKind::Absent {
                shown += 1;
                if field.kind == RowFieldKind::Present {
                    present += 1;
                }
            }
        }
        let all_present = present == shown;
        let mut flags = 0;
        if row.closed {
            flags |= CLOSED;
        }
        if all_present {
            flags |= ALL_PRESENT;
        }
        if row.name != NONE && self.namable_row(ty) {
            if !(row.closed && all_present) && self.is_non_gen(sch, px) {
                flags |= NON_GEN;
            }
            let ident = self.ident_doc(row.name, false, row.name_args.len != 0);
            self.tasks.push(Task::VariantNamed {
                ident,
                len: row.name_args.len,
                flags,
            });
            for i in (0..row.name_args.len).rev() {
                let child = self.g.ns_at(row.name_args, i);
                self.tasks.push(Task::Enter { ty: child, sch });
            }
            return;
        }
        if !(row.closed && all_present) && self.is_non_gen(sch, px) {
            flags |= NON_GEN;
        }
        let start = self.vfields.len() as u32;
        let mut tasks: smallvec::SmallVec<[Task; 8]> = smallvec::SmallVec::new();
        for i in 0..row.fields.len {
            let field = self.g.field(row.fields, i);
            if row.closed && field.kind == RowFieldKind::Absent {
                continue;
            }
            let (count, ampersand) = match field.kind {
                RowFieldKind::Either { constant: true, .. } if field.types.len == 0 => (0, false),
                RowFieldKind::Either { constant, .. } => (field.types.len, constant),
                RowFieldKind::Present => (field.types.len, false),
                RowFieldKind::Absent => (0, false),
            };
            for k in 0..count {
                tasks.push(Task::Enter {
                    ty: self.g.ns_at(field.types, k),
                    sch,
                });
            }
            self.vfields.push(VField {
                label: field.label,
                count,
                ampersand,
            });
        }
        let fields = Range {
            start,
            len: self.vfields.len() as u32 - start,
        };
        tasks.push(Task::VariantFields { fields, flags });
        self.queue(&tasks);
    }

    /// O(fields): `tree_of_typobject`.
    fn enter_object(&mut self, sch: bool, head: N) {
        let mut fields = std::mem::take(&mut self.fields);
        let rest = self.g.flatten_fields(head, &mut fields);
        let v = &self.g.v;
        fields.sort_by(|a, b| v.str(a.name).as_bytes().cmp(v.str(b.name).as_bytes()));
        let rest = match self.g.desc(rest) {
            Desc::Var(_) | Desc::Univar(_) => 1 + u8::from(self.is_non_gen(sch, rest)),
            Desc::Constr { .. } => 1,
            _ => 0,
        };
        let start = self.ofields.len() as u32;
        self.ofields.extend(fields.iter().map(|field| OField {
            name: field.name,
            mutable: field.mutable,
        }));
        self.tasks.push(Task::Object {
            fields: Range {
                start,
                len: fields.len() as u32,
            },
            rest,
        });
        for field in fields.iter().rev() {
            self.tasks.push(Task::Enter { ty: field.typ, sch });
        }
        self.fields = fields;
    }

    /// O(1): `Otyp_var`.
    fn var_doc(&mut self, non_gen: bool, name: u32) -> D {
        let text = format!(
            "{}{}",
            if non_gen { "'_" } else { "'" },
            self.names.texts[name as usize]
        );
        self.docs.text(&text)
    }

    /// O(items): `open`, the indented items separated by `,` and a line,
    /// a trailing comma, `close`, in a group.
    fn list_doc(&mut self, open: &str, items: &[D], close: &str) -> D {
        let open = self.text(open);
        let body = self.comma_join(items);
        let soft = self.docs.soft_line();
        let inner = self.docs.concat(&[soft, body]);
        let indented = self.docs.indent(inner);
        let comma = self.docs.trailing_comma();
        let soft = self.docs.soft_line();
        let close = self.text(close);
        let all = self.docs.concat(&[open, indented, comma, soft, close]);
        self.docs.group(all)
    }

    /// O(items): `Doc.join (concat [comma; line]) items`.
    fn comma_join(&mut self, items: &[D]) -> D {
        let comma = self.text(",");
        let line = self.docs.line();
        let sep = self.docs.concat(&[comma, line]);
        self.docs.join(sep, items)
    }

    /// O(args): `Otyp_constr` from the last `len` results.
    fn constr_doc(&mut self, ident: D, len: u32) -> D {
        if len == 0 {
            return ident;
        }
        let start = self.results.len() - len as usize;
        let args: smallvec::SmallVec<[D; 8]> =
            self.results[start..].iter().map(|out| out.doc).collect();
        self.results.truncate(start);
        let open = self.text("<");
        let body = self.comma_join(&args);
        let soft = self.docs.soft_line();
        let inner = self.docs.concat(&[soft, body]);
        let indented = self.docs.indent(inner);
        let comma = self.docs.trailing_comma();
        let soft = self.docs.soft_line();
        let close = self.text(">");
        let args = self.docs.concat(&[open, indented, comma, soft, close]);
        let all = self.docs.concat(&[ident, args]);
        self.docs.group(all)
    }

    /// O(1): the `Otyp_variant` frame around `body`.
    fn variant_doc(&mut self, flags: u8, body: D) -> D {
        let closed = flags & CLOSED != 0;
        let tags = flags & ALL_PRESENT == 0;
        let opening = match (closed, tags) {
            (true, false) => self.docs.soft_line(),
            (false, false) => {
                let gt = self.text(">");
                let line = self.docs.line();
                self.docs.concat(&[gt, line])
            }
            (true, true) => {
                let lt = self.text("<");
                let line = self.docs.line();
                self.docs.concat(&[lt, line])
            }
            (false, true) => {
                let q = self.text("?");
                let line = self.docs.line();
                self.docs.concat(&[q, line])
            }
        };
        let non_gen = if flags & NON_GEN != 0 {
            self.text("_")
        } else {
            self.docs.nil()
        };
        let open = self.text("[");
        let inner = self.docs.concat(&[opening, body]);
        let indented = self.docs.indent(inner);
        let soft = self.docs.soft_line();
        let close = self.text("]");
        let all = self.docs.concat(&[non_gen, open, indented, soft, close]);
        self.docs.group(all)
    }

    /// O(fields + types): `print_out_variant (Ovar_fields fields)`.
    fn variant_fields_doc(&mut self, fields: Range) -> D {
        let total: u32 = (0..fields.len)
            .map(|i| self.vfields[(fields.start + i) as usize].count)
            .sum();
        let start = self.results.len() - total as usize;
        let mut cursor = start;
        let mut parts: smallvec::SmallVec<[D; 8]> = smallvec::SmallVec::new();
        for i in 0..fields.len {
            let field = self.vfields[(fields.start + i) as usize];
            let lead = if i > 0 {
                self.text("| ")
            } else {
                let bar = self.text("| ");
                let nil = self.docs.nil();
                self.docs.if_breaks(bar, nil)
            };
            let mut text = String::from("#");
            match crate::parser::printer::print_poly_var_ident(self.g.v.str(field.label)) {
                crate::parser::doc::Doc::Text(name) => text.push_str(&name),
                doc => text.push_str(&doc.to_string(80)),
            }
            let hash = self.docs.text(&text);
            let types = &self.results[cursor..cursor + field.count as usize];
            cursor += field.count as usize;
            let body = if types.is_empty() {
                self.docs.nil()
            } else {
                let needs_parens = !(types.len() == 1 && types[0].kind == Kind::Tuple);
                let docs: smallvec::SmallVec<[D; 4]> = types.iter().map(|out| out.doc).collect();
                let mut wrapped: smallvec::SmallVec<[D; 4]> = smallvec::SmallVec::new();
                for doc in docs {
                    wrapped.push(if needs_parens {
                        let open = self.text("(");
                        let close = self.text(")");
                        self.docs.concat(&[open, doc, close])
                    } else {
                        doc
                    });
                }
                let amp = if field.ampersand {
                    self.text(" & ")
                } else {
                    self.docs.nil()
                };
                let and = self.text(" &");
                let line = self.docs.line();
                let sep = self.docs.concat(&[and, line]);
                let joined = self.docs.join(sep, &wrapped);
                let inner = self.docs.concat(&[joined]);
                let indented = self.docs.indent(inner);
                self.docs.concat(&[amp, indented])
            };
            let field_doc = self.docs.concat(&[hash, body]);
            let group = self.docs.group(field_doc);
            parts.push(self.docs.concat(&[lead, group]));
        }
        self.results.truncate(start);
        let line = self.docs.line();
        self.docs.join(line, &parts)
    }

    /// O(fields): `print_object_fields`.
    fn object_doc(&mut self, fields: Range, rest: u8) -> D {
        let start = self.results.len() - fields.len as usize;
        let mut parts: smallvec::SmallVec<[D; 8]> = smallvec::SmallVec::new();
        for i in 0..fields.len {
            let field = self.ofields[(fields.start + i) as usize];
            let doc = self.results[start + i as usize].doc;
            let set = if field.mutable {
                self.text("@set ")
            } else {
                self.docs.nil()
            };
            let text = format!("\"{}\": ", self.g.v.str(field.name));
            let label = self.docs.text(&text);
            let all = self.docs.concat(&[set, label, doc]);
            parts.push(self.docs.group(all));
        }
        self.results.truncate(start);
        let dots = match rest {
            2 => self.text("_.."),
            1 => self.text(".."),
            _ if fields.len == 0 => self.text("."),
            _ => self.docs.nil(),
        };
        let open = self.text("{");
        let body = self.comma_join(&parts);
        let soft = self.docs.soft_line();
        let inner = self.docs.concat(&[soft, body]);
        let indented = self.docs.indent(inner);
        let comma = self.docs.trailing_comma();
        let soft = self.docs.soft_line();
        let close = self.text("}");
        let all = self
            .docs
            .concat(&[open, dots, indented, comma, soft, close]);
        self.docs.group(all)
    }

    /// O(arguments): `print_out_arrow_type`.
    fn build_arrow(&mut self, params: Slots) {
        let ret = self.results.pop().expect("an arrow result");
        let start = self.results.len() - params.len as usize;
        let mut args: smallvec::SmallVec<[D; 8]> = smallvec::SmallVec::new();
        let mut single_tuple_or_arrow = false;
        let mut single_unlabelled = false;
        for i in 0..params.len {
            let out = self.results[start + i as usize];
            let (label, _) = self.g.param(params, i);
            if params.len == 1 {
                single_tuple_or_arrow = matches!(out.kind, Kind::Tuple | Kind::Arrow);
                single_unlabelled = label == NONE;
            }
            args.push(if label == NONE {
                out.doc
            } else {
                let text = format!("~{}: ", self.g.v.str(label >> 1));
                let head = self.docs.text(&text);
                let tail = if label & 1 != 0 {
                    self.text("=?")
                } else {
                    self.docs.nil()
                };
                let all = self.docs.concat(&[head, out.doc, tail]);
                self.docs.group(all)
            });
        }
        self.results.truncate(start);
        let args = self.comma_join(&args);
        let needs_parens = single_tuple_or_arrow || !single_unlabelled;
        let args_doc = if needs_parens {
            let open = self.text("(");
            let soft = self.docs.soft_line();
            let inner = self.docs.concat(&[soft, args]);
            let indented = self.docs.indent(inner);
            let comma = self.docs.trailing_comma();
            let soft = self.docs.soft_line();
            let close = self.text(")");
            let all = self.docs.concat(&[open, indented, comma, soft, close]);
            self.docs.group(all)
        } else {
            args
        };
        let arrow = self.text(" => ");
        let doc = self.docs.concat(&[args_doc, arrow, ret.doc]);
        self.results.push(Out {
            doc,
            kind: Kind::Arrow,
        });
    }

    /// O(constraints + arguments): `Otyp_module`.
    fn module_doc(&mut self, docs: Range, args: u32) -> D {
        let start = self.results.len() - args as usize;
        let lids = docs.len - 1;
        let head = self.dpool[docs.start as usize];
        let package = if lids == 0 && args == 0 {
            self.docs.nil()
        } else {
            let mut parts: smallvec::SmallVec<[D; 4]> = smallvec::SmallVec::new();
            for i in 0..lids.min(args) {
                let lid = self.dpool[(docs.start + 1 + i) as usize];
                let ty = self.results[start + i as usize].doc;
                let lead = self.text(if i > 0 { "and type " } else { "with type " });
                let eq = self.text(" = ");
                parts.push(self.docs.concat(&[lead, lid, eq, ty]));
            }
            let line = self.docs.line();
            let joined = self.docs.join(line, &parts);
            let line = self.docs.line();
            let inner = self.docs.concat(&[line, joined]);
            self.docs.indent(inner)
        };
        self.results.truncate(start);
        let module = self.text("module");
        let open = self.text("(");
        let close = self.text(")");
        self.docs.concat(&[module, open, head, package, close])
    }

    /// O(components): `Longident.flatten` joined with dots. A component the
    /// pool's name table did not hold prints `<unresolved>` (the old printer
    /// prints `#` and the component's raw index, which a segment does not
    /// carry).
    fn flatten_longident(&self, out: &mut String, lid: u32) {
        let mut parts: smallvec::SmallVec<[u32; 8]> = smallvec::SmallVec::new();
        let mut current = lid;
        loop {
            match self.g.v.longident(current) {
                LongidentRow::Ident(name) => {
                    parts.push(name);
                    break;
                }
                LongidentRow::Unresolved => {
                    parts.push(NONE);
                    break;
                }
                LongidentRow::Dot { parent, name } => {
                    parts.push(name);
                    current = parent;
                }
                // `Longident.flat` rejects an application.
                LongidentRow::Apply { .. } => {
                    parts.push(NONE);
                    break;
                }
            }
        }
        for (index, part) in parts.iter().rev().enumerate() {
            if index > 0 {
                out.push('.');
            }
            out.push_str(if *part == NONE {
                "<unresolved>"
            } else {
                self.g.v.str(*part)
            });
        }
    }

    // ------------------------------------------------------------------
    // Records and constructors
    // ------------------------------------------------------------------

    /// O(labels): `print_record_declaration_doc inline rows` from the last
    /// `labels.len` results.
    fn record_rows(&mut self, labels: Range, inline: bool) -> D {
        let start = self.results.len() - labels.len as usize;
        let mut rows: smallvec::SmallVec<[D; 8]> = smallvec::SmallVec::new();
        for i in 0..labels.len {
            let label = self.g.v.p.labels[(labels.start + i) as usize];
            let ty = self.results[start + i as usize].doc;
            let mut text = String::new();
            if label.runtime_name != NONE {
                text.push_str("@as(");
                Self::string_literal(&mut text, self.g.v.str(label.runtime_name));
                text.push_str(") ");
            }
            if label.mutable {
                text.push_str("mutable ");
            }
            Self::ident_like(
                &mut text,
                self.g.v.str(self.g.v.ident(label.ident).name),
                false,
            );
            if label.optional {
                text.push('?');
            }
            text.push_str(": ");
            let head = self.docs.text(&text);
            let all = self.docs.concat(&[head, ty]);
            rows.push(self.docs.group(all));
        }
        self.results.truncate(start);
        let open = self.text("{");
        let body = self.comma_join(&rows);
        let soft = self.docs.soft_line();
        let inner = self.docs.concat(&[soft, body]);
        let indented = self.docs.indent(inner);
        let comma = self.docs.trailing_comma();
        let soft = self.docs.soft_line();
        let close = self.text("}");
        let content = self.docs.concat(&[open, indented, comma, soft, close]);
        if inline {
            content
        } else {
            self.docs.group(content)
        }
    }

    /// `tree_of_constructor_arguments`: the argument outcomes, in order, on
    /// the result stack; returns how many.
    fn constructor_arguments(&mut self, row: u32) -> u32 {
        match self.g.v.p.constructor_arguments[row as usize] {
            crate::tc::segment::ConstructorArgumentsRow::Tuple(roots) => {
                for i in 0..roots.len {
                    let ty = self.g.v.root_at(roots.start + i);
                    let out = self.tree(false, ty);
                    self.results.push(out);
                }
                roots.len
            }
            crate::tc::segment::ConstructorArgumentsRow::Record(labels) => {
                // `Cstr_record l -> [Otyp_record ...]` drops the printing context.
                let saved = self.inlined.take();
                for i in 0..labels.len {
                    let label = self.g.v.p.labels[(labels.start + i) as usize];
                    let ty = self.label_type(label.ty, label.optional);
                    let out = self.tree(false, ty);
                    self.results.push(out);
                }
                self.inlined = saved;
                let doc = self.record_rows(labels, true);
                self.results.push(Out {
                    doc,
                    kind: Kind::Record,
                });
                1
            }
        }
    }

    /// `print_out_constructor_doc` of (name, the last `args` results, gadt
    /// result, repr).
    fn constructor_doc(&mut self, name: &str, args: u32, gadt: Option<D>, repr: Option<&str>) -> D {
        let start = self.results.len() - args as usize;
        let repr = match repr {
            Some(repr) => {
                let text = format!("{repr} ");
                self.docs.text(&text)
            }
            None => self.docs.nil(),
        };
        let gadt = match gadt {
            Some(doc) => {
                let colon = self.text(": ");
                self.docs.concat(&[colon, doc])
            }
            None => self.docs.nil(),
        };
        let outs: smallvec::SmallVec<[Out; 4]> = self.results[start..].iter().copied().collect();
        self.results.truncate(start);
        let args = match outs.as_slice() {
            [] => self.docs.nil(),
            [
                Out {
                    doc,
                    kind: Kind::Record,
                },
            ] => {
                let open = self.text("(");
                let indented = self.docs.indent(*doc);
                let close = self.text(")");
                self.docs.concat(&[open, indented, close])
            }
            outs => {
                let docs: smallvec::SmallVec<[D; 4]> = outs.iter().map(|out| out.doc).collect();
                let open = self.text("(");
                let body = self.comma_join(&docs);
                let soft = self.docs.soft_line();
                let inner = self.docs.concat(&[soft, body]);
                let indented = self.docs.indent(inner);
                let comma = self.docs.trailing_comma();
                let soft = self.docs.soft_line();
                let close = self.text(")");
                let all = self.docs.concat(&[open, indented, comma, soft, close]);
                self.docs.indent(all)
            }
        };
        let name = self.text(name);
        let all = self.docs.concat(&[repr, name, args, gadt]);
        self.docs.group(all)
    }

    /// O(constructors): `print_out_constructors_doc`.
    fn constructors_doc(&mut self, constructors: &[D]) -> D {
        let mut parts: smallvec::SmallVec<[D; 8]> = smallvec::SmallVec::new();
        for (i, constructor) in constructors.iter().enumerate() {
            let lead = if i > 0 {
                self.text("| ")
            } else {
                let bar = self.text("| ");
                let nil = self.docs.nil();
                self.docs.if_breaks(bar, nil)
            };
            parts.push(self.docs.concat(&[lead, *constructor]));
        }
        let line = self.docs.line();
        let joined = self.docs.join(line, &parts);
        let soft = self.docs.soft_line();
        let inner = self.docs.concat(&[soft, joined]);
        let indented = self.docs.indent(inner);
        self.docs.group(indented)
    }

    /// O(1): the `@as` of a constructor (printtyp.rs `tree_of_constructor`).
    fn as_annotation(&self, out: &mut String, literal: u32) {
        let v = &self.g.v;
        match v.p.literals[literal as usize] {
            LiteralRow::Null => out.push_str("@as(null)"),
            LiteralRow::Undefined => out.push_str("@as(undefined)"),
            LiteralRow::String(s) => {
                out.push_str("@as(");
                Self::string_literal(out, v.str(s));
                out.push(')');
            }
            LiteralRow::Int(i) => out.push_str(&format!("@as({i})")),
            LiteralRow::Float(f) => out.push_str(&format!("@as({})", v.str(f))),
            LiteralRow::Bool(b) => out.push_str(&format!("@as({b})")),
            LiteralRow::BigInt(s) => out.push_str(&format!("@as({}n)", v.str(s))),
        }
    }

    // ------------------------------------------------------------------
    // Items
    // ------------------------------------------------------------------

    /// O(params): `filter_params`: a repeated parameter becomes a `Tsubst`.
    fn filter_params(&mut self, roots: Range) {
        self.params.clear();
        for i in 0..roots.len {
            let ty = self.g.v.root_at(roots.start + i);
            let ty = if self.params.contains(&ty) {
                self.g.make_subst(ty)
            } else {
                ty
            };
            self.params.push(ty);
        }
    }

    /// The parameter name of `tree_of_typexp false p` (`?` if not a variable).
    fn param_name(&mut self, p: N) -> String {
        let out = self.tree(false, p);
        match out.kind {
            Kind::Var(name) => self.names.texts[name as usize].clone(),
            _ => "?".to_string(),
        }
    }

    /// O(the value's type): `tree_of_value_description` printed.
    fn value(&mut self, name: &str, row: u32) -> D {
        let value = self.g.v.p.values[row as usize];
        let ty = self.g.v.root_at(value.ty);
        self.reset();
        self.mark_loops(ty);
        let typ = self.tree(true, ty);
        let mut attrs = String::new();
        let mut keyword = "let ";
        let mut prim_name: Option<&str> = None;
        if value.primitive != NONE {
            let prim = self.g.v.p.primitives[value.primitive as usize];
            let pname = self.g.v.str(prim.name);
            match prim.kind {
                PrimitiveKindRow::Intrinsic => {
                    keyword = "external ";
                    prim_name = Some(pname);
                }
                PrimitiveKindRow::Inline(constant) => {
                    attrs.push_str("@inline(");
                    self.inline_constant(&mut attrs, constant);
                    attrs.push_str(") ");
                }
                PrimitiveKindRow::External(ffi) => {
                    keyword = "external ";
                    prim_name = Some(pname);
                    match self.g.v.p.ffi[ffi as usize] {
                        FfiRow::Object(_) => attrs.push_str("@obj "),
                        FfiRow::Call {
                            declaration,
                            return_wrapper,
                            ..
                        } => {
                            self.external_attributes(&mut attrs, declaration, return_wrapper, pname)
                        }
                    }
                }
            }
        }
        let attrs = self.docs.text(&attrs);
        let keyword = self.docs.text(keyword);
        let name = self.docs.text(name);
        let colon = self.text(":");
        let space = self.text(" ");
        let prim = match prim_name {
            None => self.docs.nil(),
            Some(prim) => {
                let eq = self.text(" =");
                let line = self.docs.line();
                let text = format!("\"{prim}\"");
                let quoted = self.docs.text(&text);
                let group = self.docs.group(quoted);
                let inner = self.docs.concat(&[eq, line, group]);
                self.docs.indent(inner)
            }
        };
        let all = self
            .docs
            .concat(&[attrs, keyword, name, colon, space, typ.doc, prim]);
        self.docs.group(all)
    }

    /// O(1): `print_inline_const_doc`.
    fn inline_constant(&self, out: &mut String, row: u32) {
        let v = &self.g.v;
        match v.p.inline_constants[row as usize] {
            InlineConstantRow::String(s) => Self::string_literal(out, v.str(s)),
            InlineConstantRow::Bool(b) => out.push_str(if b { "true" } else { "false" }),
            InlineConstantRow::Int(i) => out.push_str(&i.to_string()),
            InlineConstantRow::Bigint { positive, digits } => {
                if !positive {
                    out.push('-');
                }
                out.push_str(v.str(digits));
                out.push('n');
            }
            InlineConstantRow::Float(f) => out.push_str(v.str(f)),
        }
    }

    /// O(the declaration): `print_external_decl_attrs_doc`, as text.
    fn external_attributes(
        &self,
        out: &mut String,
        row: u32,
        wrapper: ReturnWrapperRow,
        prim: &str,
    ) {
        let v = &self.g.v;
        let decl = v.p.external_declarations[row as usize];
        let with_payload = |out: &mut String, attr: &str, name: u32| {
            let name = v.str(name);
            if name == prim {
                out.push('@');
                out.push_str(attr);
                out.push(' ');
            } else {
                out.push('@');
                out.push_str(attr);
                out.push('(');
                Self::string_literal(out, name);
                out.push_str(") ");
            }
        };
        match decl.kind {
            ExternalKindRow::Value(name) => {
                if decl.module != ModuleSourceRow::Itself {
                    with_payload(out, "val", name);
                }
            }
            ExternalKindRow::Send(name) => with_payload(out, "send", name),
            ExternalKindRow::New(name) => with_payload(out, "new", name),
            ExternalKindRow::Get(name) => with_payload(out, "get", name),
            ExternalKindRow::Set(name) => with_payload(out, "set", name),
            ExternalKindRow::GetIndex => out.push_str("@get_index "),
            ExternalKindRow::SetIndex => out.push_str("@set_index "),
        }
        match decl.module {
            ModuleSourceRow::Absent => {}
            ModuleSourceRow::Itself => out.push_str("@module "),
            ModuleSourceRow::Named(module) => {
                let module = v.p.external_modules[module as usize];
                out.push_str("@module(");
                let bundle = v.str(module.bundle);
                if module.import_attributes == NONE {
                    if module.binding_hint == NONE {
                        Self::string_literal(out, bundle);
                    } else {
                        out.push('(');
                        Self::string_literal(out, bundle);
                        out.push_str(", ");
                        Self::string_literal(out, v.str(module.binding_hint));
                        out.push(')');
                    }
                } else {
                    out.push_str("{from: ");
                    Self::string_literal(out, bundle);
                    if module.binding_hint != NONE {
                        out.push_str(", as: ");
                        Self::string_literal(out, v.str(module.binding_hint));
                    }
                    out.push_str(", with: {");
                    let pairs = v.p.ranges[module.import_attributes as usize];
                    for i in 0..pairs.len {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        let pair = v.p.string_pairs[(pairs.start + i) as usize];
                        let key = v.str(pair.first);
                        if key == "type" {
                            out.push_str("type_");
                        } else {
                            Self::ident_like(out, key, false);
                        }
                        out.push_str(": ");
                        Self::string_literal(out, v.str(pair.second));
                    }
                    out.push_str("}}");
                }
                out.push_str(") ");
            }
        }
        match decl.scopes.len {
            0 => {}
            1 => {
                out.push_str("@scope(");
                Self::string_literal(out, v.str(v.p.indices[decl.scopes.start as usize]));
                out.push_str(") ");
            }
            len => {
                out.push_str("@scope((");
                for i in 0..len {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    Self::string_literal(out, v.str(v.p.indices[(decl.scopes.start + i) as usize]));
                }
                out.push_str(")) ");
            }
        }
        if decl.variadic {
            out.push_str("@variadic ");
        }
        out.push_str(match wrapper {
            ReturnWrapperRow::Unset => "",
            ReturnWrapperRow::Identity => "@return(identity) ",
            ReturnWrapperRow::NullToOption => "@return(null_to_opt) ",
            ReturnWrapperRow::NullUndefinedToOption => "@return(nullable) ",
        });
    }

    /// O(params + their nodes): `tree_of_constraints`, in its reverse order.
    fn constraints(&mut self) -> D {
        let mut pairs: smallvec::SmallVec<[D; 4]> = smallvec::SmallVec::new();
        for index in (0..self.params.len()).rev() {
            let ty = self.params[index];
            let ty2 = self.unalias(ty);
            if self.g.proxy(ty) != self.g.proxy(ty2) {
                let tr = self.tree(true, ty);
                let tr2 = self.tree(true, ty2);
                let head = self.text("constraint ");
                let eq = self.text(" =");
                let space = self.text(" ");
                let all = self.docs.concat(&[head, tr.doc, eq, space, tr2.doc]);
                pairs.push(self.docs.group(all));
            }
        }
        if pairs.is_empty() {
            return self.docs.nil();
        }
        pairs.reverse();
        let hard = self.docs.hard_line();
        let line = self.docs.line();
        let joined = self.docs.join(line, &pairs);
        let inner = self.docs.concat(&[hard, joined]);
        let indented = self.docs.indent(inner);
        self.docs.group(indented)
    }

    /// O(the object chain): `Ctype.unalias` (printtyp.rs:2709).
    fn unalias(&mut self, ty: N) -> N {
        let level = self.g.level(ty);
        match self.g.desc(ty) {
            Desc::Var(_) | Desc::Univar(_) => ty,
            Desc::Variant => {
                let row = self.g.row(ty);
                let more = self.g.make_copy(row.more);
                let index = self.g.push_row(super::view::Row { more, ..row });
                self.g.make_variant(index, level)
            }
            Desc::Object(fields) => {
                let fields_level = self.g.level(fields);
                let fields = self.unalias_object(fields);
                self.g.make_object(fields, fields_level)
            }
            _ => self.g.make_copy(ty),
        }
    }

    /// O(fields): `unalias_object`, building the copied chain from its end.
    fn unalias_object(&mut self, ty: N) -> N {
        let mut chain: smallvec::SmallVec<[(u32, bool, N); 8]> = smallvec::SmallVec::new();
        let mut current = ty;
        while let Desc::Field {
            name,
            mutable,
            typ,
            rest,
        } = self.g.desc(current)
        {
            chain.push((name, mutable, typ));
            current = rest;
        }
        let mut rest = match self.g.desc(current) {
            Desc::Var(_) | Desc::Nil => self.g.make_copy(current),
            Desc::Univar(_) => current,
            _ => {
                let level = self.g.level(current);
                self.g.make_var(level)
            }
        };
        for &(name, mutable, typ) in chain.iter().rev() {
            rest = self.g.make_field(name, mutable, typ, rest);
        }
        rest
    }

    /// `tree_of_type_decl`, printed as `Osig_type`.
    fn type_declaration(&mut self, item_ident: u32, index: u32, status: u8) -> D {
        let decl = self.g.v.seg.type_declarations[index as usize];
        let details = self.g.v.p.type_details[index as usize];
        let name = self.str(self.g.v.ident(item_ident).name);
        self.reset();
        let saved_inlined = self.inlined.replace(details.inlined_records);
        self.filter_params(details.parameter_roots);
        if decl.manifest != NONE {
            let manifest = self.g.v.root_at(decl.manifest);
            let mut free = std::mem::take(&mut self.free);
            let mut marks = std::mem::take(&mut self.free_marks);
            self.g.free_variables(manifest, &mut marks, &mut free);
            // Membership in the free variables, reusing the visit marks.
            marks.clear();
            for &var in &free {
                marks.insert(var);
            }
            for i in 0..self.params.len() {
                let param = self.params[i];
                if let Desc::Var(given) = self.g.desc(param)
                    && given != NONE
                    && self.g.v.str(given) == "_"
                    && marks.has(param)
                {
                    self.g.unname(param);
                }
            }
            self.free = free;
            self.free_marks = marks;
        }
        let params = self.params.clone();
        for &param in &params {
            self.add_alias(param);
        }
        for &param in &params {
            self.mark_loops(param);
        }
        for &param in &params {
            let px = self.g.proxy(param);
            self.name_of_type(false, px);
        }
        let manifest = if decl.manifest == NONE {
            None
        } else {
            let ty = self.g.v.root_at(decl.manifest);
            // Special hack to hide variant name.
            let ty = match self.g.desc(ty) {
                Desc::Variant => {
                    let row = self.g.row(ty);
                    match row.name {
                        NONE => ty,
                        path => match self.g.v.path(path) {
                            PathRow::Ident(id) if self.g.v.same_ident(id, item_ident) => {
                                let index = self.g.push_row(super::view::Row { name: NONE, ..row });
                                self.g.make_variant(index, GENERIC)
                            }
                            _ => ty,
                        },
                    }
                }
                _ => ty,
            };
            self.mark_loops(ty);
            Some(ty)
        };
        let members = Range {
            start: decl.members,
            len: decl.member_len,
        };
        match decl.kind {
            DeclarationKind::Abstract | DeclarationKind::Open => {}
            DeclarationKind::Variant => {
                for i in 0..members.len {
                    let member = self.g.v.seg.members[(members.start + i) as usize];
                    let constructor = self.g.v.p.constructors[member.args as usize];
                    self.mark_constructor_arguments(constructor.arguments);
                    if constructor.result != NONE {
                        let res = self.g.v.root_at(constructor.result);
                        self.mark_loops(res);
                    }
                }
            }
            DeclarationKind::Record => {
                for i in 0..members.len {
                    let member = self.g.v.seg.members[(members.start + i) as usize];
                    let label = self.g.v.p.labels[member.args as usize];
                    let ty = self.g.v.root_at(label.ty);
                    self.mark_loops(ty);
                }
            }
        }
        let private = decl.flags & 1 != 0;
        let has_gadt = decl.kind == DeclarationKind::Variant
            && (0..members.len).any(|i| {
                let member = self.g.v.seg.members[(members.start + i) as usize];
                self.g.v.p.constructors[member.args as usize].result != NONE
            });
        let abstr = match decl.kind {
            DeclarationKind::Abstract => decl.manifest == NONE || private,
            DeclarationKind::Record => private,
            DeclarationKind::Variant => private || has_gadt,
            DeclarationKind::Open => decl.manifest == NONE,
        };
        let mut param_docs: smallvec::SmallVec<[D; 4]> = smallvec::SmallVec::new();
        let count = details.parameter_roots.len.min(details.variance.len);
        let mut variances: smallvec::SmallVec<[(bool, bool); 4]> = smallvec::SmallVec::new();
        for i in 0..count {
            let original = self.g.v.root_at(details.parameter_roots.start + i);
            let bits = self.g.v.p.variance[(details.variance.start + i) as usize];
            let is_var = matches!(self.g.desc(original), Desc::Var(_));
            variances.push(if abstr || !is_var {
                (bits & 1 != 0, bits & 2 != 0)
            } else {
                (true, true)
            });
        }
        for (i, (co, cn)) in variances.iter().copied().enumerate() {
            let name = self.param_name(params[i]);
            let mut text = String::new();
            if !cn {
                text.push('+');
            } else if !co {
                text.push('-');
            }
            if name == "_" {
                text.push('_');
            } else {
                text.push('\'');
                text.push_str(&name);
            }
            param_docs.push(self.docs.text(&text));
        }
        let constraints = self.constraints();
        let unboxed_flag = decl.flags & 4 != 0;
        let private_doc = |this: &mut Self| {
            if private {
                this.text("private ")
            } else {
                this.docs.nil()
            }
        };
        let (kind, unboxed) = match decl.kind {
            DeclarationKind::Abstract => match manifest {
                None => (self.docs.nil(), unboxed_flag),
                Some(ty) => {
                    let out = self.tree(false, ty);
                    let typ = if out.kind == Kind::Record {
                        self.docs.group(out.doc)
                    } else {
                        out.doc
                    };
                    let eq = self.text(" = ");
                    let private = private_doc(self);
                    (self.docs.concat(&[eq, private, typ]), unboxed_flag)
                }
            },
            DeclarationKind::Variant => {
                let layout = details.representation;
                let layout_row = self.g.v.p.layouts[layout as usize];
                let mut constructors: smallvec::SmallVec<[D; 8]> = smallvec::SmallVec::new();
                for i in 0..members.len {
                    let member = self.g.v.seg.members[(members.start + i) as usize];
                    let doc = self.constructor(member.args, layout, i);
                    constructors.push(doc);
                }
                let sum = self.constructors_doc(&constructors);
                let kind = self.manifest_kind(manifest, sum, private);
                (kind, unboxed_flag || layout_row.unboxed)
            }
            DeclarationKind::Record => {
                let labels = if members.len == 0 {
                    Range::default()
                } else {
                    Range {
                        start: self.g.v.seg.members[members.start as usize].args,
                        len: members.len,
                    }
                };
                for i in 0..labels.len {
                    let label = self.g.v.p.labels[(labels.start + i) as usize];
                    let ty = self.label_type(label.ty, label.optional);
                    let out = self.tree(false, ty);
                    self.results.push(out);
                }
                let kind = match manifest {
                    None => {
                        let record = self.record_rows(labels, false);
                        let eq = self.text(" = ");
                        let private = private_doc(self);
                        self.docs.concat(&[eq, private, record])
                    }
                    Some(_) => {
                        let record = self.record_rows(labels, true);
                        self.manifest_kind(manifest, record, private)
                    }
                };
                (kind, unboxed_flag)
            }
            DeclarationKind::Open => {
                let kind = match manifest {
                    None => {
                        let eq = self.text(" = ");
                        let private = private_doc(self);
                        let dots = self.text("..");
                        self.docs.concat(&[eq, private, dots])
                    }
                    Some(_) => {
                        let nil = self.docs.nil();
                        self.manifest_kind(manifest, nil, private)
                    }
                };
                (kind, unboxed_flag)
            }
        };
        // What the declaration itself states (printtyp.rs:1146-1176).
        let mut attributes: smallvec::SmallVec<[String; 2]> = smallvec::SmallVec::new();
        let attrs = details.attributes;
        let p = self.g.v.p;
        let attr_rows = &p.attributes[attrs.start as usize..(attrs.start + attrs.len) as usize];
        if attr_rows
            .iter()
            .any(|attr| self.g.v.str(attr.name) == "immediate")
        {
            attributes.push("@immediate".to_string());
        }
        if unboxed {
            attributes.push("@unboxed".to_string());
        }
        if let Some(tag) = self.variant_tag_name(attrs) {
            attributes.push(format!(
                "@tag(\"{}\")",
                crate::string_literal::encode_js_string(tag)
            ));
        }
        if let Some(annotation) = self.runtime_annotation(attrs) {
            attributes.push(annotation);
        }
        self.inlined = saved_inlined;
        let attrs = if attributes.is_empty() {
            self.docs.nil()
        } else {
            let text = self.docs.text(&attributes.join(" "));
            let line = self.docs.line();
            self.docs.concat(&[text, line])
        };
        let keyword = self.text(match status {
            1 => "type rec ",
            2 => "and ",
            _ => "type ",
        });
        let mut ident = String::new();
        Self::ident_like(&mut ident, name, false);
        let ident = self.docs.text(&ident);
        let params = if param_docs.is_empty() {
            self.docs.nil()
        } else {
            let open = self.text("<");
            let body = self.comma_join(&param_docs);
            let soft = self.docs.soft_line();
            let inner = self.docs.concat(&[soft, body]);
            let indented = self.docs.indent(inner);
            let comma = self.docs.trailing_comma();
            let soft = self.docs.soft_line();
            let close = self.text(">");
            let all = self.docs.concat(&[open, indented, comma, soft, close]);
            self.docs.group(all)
        };
        let head = self.docs.concat(&[keyword, ident, params, kind]);
        let head = self.docs.group(head);
        let all = self.docs.concat(&[attrs, head, constraints]);
        self.docs.group(all)
    }

    /// `Otyp_manifest (manifest, typ)` (or `typ` alone) as a declaration
    /// kind: ` = manifest = private typ`. The manifest's tree is made after
    /// the kind's, as `tree_of_manifest` does.
    fn manifest_kind(&mut self, manifest: Option<N>, typ: D, private: bool) -> D {
        let eq = self.text(" = ");
        let private = if private {
            self.text("private ")
        } else {
            self.docs.nil()
        };
        match manifest {
            None => self.docs.concat(&[eq, private, typ]),
            Some(ty) => {
                let out = self.tree(false, ty);
                let eq2 = self.text(" = ");
                self.docs.concat(&[eq, out.doc, eq2, private, typ])
            }
        }
    }

    /// `mark_loops_constructor_arguments`.
    fn mark_constructor_arguments(&mut self, row: u32) {
        match self.g.v.p.constructor_arguments[row as usize] {
            crate::tc::segment::ConstructorArgumentsRow::Tuple(roots) => {
                for i in 0..roots.len {
                    let ty = self.g.v.root_at(roots.start + i);
                    self.mark_loops(ty);
                }
            }
            crate::tc::segment::ConstructorArgumentsRow::Record(labels) => {
                for i in 0..labels.len {
                    let label = self.g.v.p.labels[(labels.start + i) as usize];
                    let ty = self.g.v.root_at(label.ty);
                    self.mark_loops(ty);
                }
            }
        }
    }

    /// `tree_of_constructor`, printed.
    fn constructor(&mut self, row: u32, layout: u32, position: u32) -> D {
        let constructor = self.g.v.p.constructors[row as usize];
        let name = self.str(self.g.v.ident(constructor.ident).name);
        let nullary = matches!(
            self.g.v.p.constructor_arguments[constructor.arguments as usize],
            crate::tc::segment::ConstructorArgumentsRow::Tuple(roots) if roots.len == 0
        );
        let layout = self.g.v.p.layouts[layout as usize];
        let tagged_block = position < layout.constructors.len
            && matches!(
                self.g.v.p.runtime_constructors[(layout.constructors.start + position) as usize],
                RuntimeConstructorRow::Tagged { .. }
            );
        let mut repr = String::new();
        if (nullary || tagged_block) && constructor.runtime_tag != NONE {
            self.as_annotation(&mut repr, constructor.runtime_tag);
        }
        let repr = (!repr.is_empty()).then_some(repr);
        if constructor.result == NONE {
            let args = self.constructor_arguments(constructor.arguments);
            self.constructor_doc(name, args, None, repr.as_deref())
        } else {
            let saved = self.names.take();
            let res = self.g.v.root_at(constructor.result);
            let ret = self.tree(false, res);
            let args = self.constructor_arguments(constructor.arguments);
            self.names.restore(saved);
            self.constructor_doc(name, args, Some(ret.doc), repr.as_deref())
        }
    }

    /// `Ast_untagged_variants.process_tag_name`: the one `@tag` string.
    fn variant_tag_name(&self, attrs: Range) -> Option<&'s str> {
        let v = &self.g.v;
        let mut tag = None;
        for i in 0..attrs.len {
            let attr = v.p.attributes[(attrs.start + i) as usize];
            if v.str(attr.name) != "tag" {
                continue;
            }
            if tag.is_some() {
                return None;
            }
            match self.semantic_string(attr.payload) {
                Ok(Some(value)) => tag = Some(value),
                Ok(None) | Err(()) => return None,
            }
        }
        tag
    }

    /// `AttributePayload::semantic_string`: Err for an invalid template.
    fn semantic_string(&self, payload: u32) -> Result<Option<&'s str>, ()> {
        let v = &self.g.v;
        match v.p.attribute_payloads[payload as usize] {
            AttributePayloadRow::Str(s) => Ok(Some(v.str(s))),
            AttributePayloadRow::SemanticString(row) => {
                match v.p.semantic_strings[row as usize].value {
                    SemanticStringValue::Valid(s) => Ok(Some(v.str(s))),
                    SemanticStringValue::Missing | SemanticStringValue::Invalid(_) => Err(()),
                }
            }
            _ => Ok(None),
        }
    }

    /// `stated_runtime_annotation` (variant_layout.rs:298): the one valid
    /// `@notUndefined`, `@instanceOf` or `@typeOf`, as written.
    fn runtime_annotation(&self, attrs: Range) -> Option<String> {
        let v = &self.g.v;
        let mut found: Option<String> = None;
        let mut count = 0;
        for i in 0..attrs.len {
            let attr = v.p.attributes[(attrs.start + i) as usize];
            let annotation = match v.str(attr.name) {
                "notUndefined" => "@notUndefined".to_string(),
                "instanceOf" => match self.semantic_string(attr.payload) {
                    Ok(Some(name)) if is_class_path(name) && supported_class(name) => {
                        format!("@instanceOf(\"{name}\")")
                    }
                    _ => return None,
                },
                "typeOf" => match self.semantic_string(attr.payload) {
                    Ok(Some(name))
                        if matches!(
                            name,
                            "string"
                                | "number"
                                | "bigint"
                                | "boolean"
                                | "symbol"
                                | "function"
                                | "object"
                        ) =>
                    {
                        format!("@typeOf(\"{name}\")")
                    }
                    _ => return None,
                },
                _ => continue,
            };
            count += 1;
            found = Some(annotation);
        }
        if count == 1 { found } else { None }
    }

    /// `tree_of_extension_constructor`, as a signature item.
    fn extension(&mut self, item_ident: u32, row: u32, status: u8) -> SigOut {
        let ext = self.g.v.p.extensions[row as usize];
        let name = self.str(self.g.v.ident(item_ident).name);
        self.reset();
        let mut type_name = String::new();
        self.path_name(&mut type_name, ext.path, false);
        self.filter_params(ext.parameters);
        let params = self.params.clone();
        for &param in &params {
            self.add_alias(param);
        }
        for &param in &params {
            self.mark_loops(param);
        }
        for &param in &params {
            let px = self.g.proxy(param);
            self.name_of_type(false, px);
        }
        self.mark_constructor_arguments(ext.arguments);
        if ext.result != NONE {
            let res = self.g.v.root_at(ext.result);
            self.mark_loops(res);
        }
        let mut param_docs: smallvec::SmallVec<[D; 4]> = smallvec::SmallVec::new();
        for &param in &params {
            let name = self.param_name(param);
            let text = if name == "_" {
                name
            } else {
                format!("'{name}")
            };
            param_docs.push(self.docs.text(&text));
        }
        let constructor = if ext.result == NONE {
            let args = self.constructor_arguments(ext.arguments);
            self.constructor_doc(name, args, None, None)
        } else {
            let saved = self.names.take();
            let res = self.g.v.root_at(ext.result);
            let ret = self.tree(false, res);
            let args = self.constructor_arguments(ext.arguments);
            self.names.restore(saved);
            self.constructor_doc(name, args, Some(ret.doc), None)
        };
        let mut ident = String::new();
        Self::ident_like(&mut ident, &type_name, false);
        let ident = self.docs.text(&ident);
        let params = if param_docs.is_empty() {
            self.docs.nil()
        } else {
            let open = self.text("<");
            let body = self.comma_join(&param_docs);
            let soft = self.docs.soft_line();
            let inner = self.docs.concat(&[soft, body]);
            let indented = self.docs.indent(inner);
            let soft = self.docs.soft_line();
            let close = self.text(">");
            let all = self.docs.concat(&[open, indented, soft, close]);
            self.docs.group(all)
        };
        let header = self.docs.concat(&[ident, params]);
        SigOut::Ext {
            constructor,
            header,
            status,
            private: ext.private,
        }
    }

    // ------------------------------------------------------------------
    // Signatures and module types
    // ------------------------------------------------------------------

    /// The printed text of the unit's signature: `print_out_module_type
    /// (tree_of_modtype_in_unit (Mty_signature sg) unit)`. O(items + their
    /// types), explicit step and frame stacks whatever the nesting.
    pub fn run(mut self, top: u32) -> String {
        self.prefixes.clear();
        let mut steps: Vec<Step> = Vec::new();
        self.open_signature(top, &mut steps);
        while let Some(step) = steps.pop() {
            match step {
                Step::Next => self.next_item(&mut steps),
                Step::Mty { row, ellipsis } => self.module_type(row, ellipsis, &mut steps),
                Step::Module {
                    name,
                    status,
                    scoped,
                } => {
                    let mty = self.mtys.pop().expect("a module type");
                    if scoped {
                        self.prefixes.pop();
                    }
                    let name = self.str(name);
                    let doc = match mty {
                        Mty::Alias(ident) => {
                            let text = format!("module {name} =");
                            let head = self.docs.text(&text);
                            let line = self.docs.line();
                            let all = self.docs.concat(&[head, line, ident]);
                            self.docs.group(all)
                        }
                        mty => {
                            let keyword = match status {
                                1 => "module rec ",
                                2 => "and ",
                                _ => "module ",
                            };
                            let text = format!("{keyword}{name}: ");
                            let head = self.docs.text(&text);
                            let body = self.mty_doc(mty);
                            let all = self.docs.concat(&[head, body]);
                            self.docs.group(all)
                        }
                    };
                    self.items.push(SigOut::Doc(doc));
                }
                Step::ModuleTypeDecl { name } => {
                    let mty = self.mtys.pop().expect("a module type");
                    let name = self.str(name);
                    let doc = match mty {
                        Mty::EmptySignature => {
                            let text = format!("module type {name}");
                            self.docs.text(&text)
                        }
                        mty => {
                            let text = format!("module type {name} = ");
                            let head = self.docs.text(&text);
                            let body = self.mty_doc(mty);
                            let all = self.docs.concat(&[head, body]);
                            self.docs.group(all)
                        }
                    };
                    self.items.push(SigOut::Doc(doc));
                }
                Step::Functor { param, has_type } => {
                    let arg = if has_type {
                        let mty = self.mtys.pop().expect("a parameter type");
                        Some(self.mty_doc(mty))
                    } else {
                        None
                    };
                    let result = self.mtys.pop().expect("a functor result");
                    let (next, result) = match result {
                        Mty::Functor { params, result } => (params, result),
                        mty => (NONE, self.mty_doc(mty)),
                    };
                    let head = self.functor_params.len() as u32;
                    self.functor_params.push(FunctorParam {
                        name: self.g.v.ident(param).name,
                        arg,
                        next,
                    });
                    self.mtys.push(Mty::Functor {
                        params: head,
                        result,
                    });
                }
            }
        }
        let top = self.mtys.pop().expect("the unit's signature");
        let doc = self.mty_doc(top);
        self.docs.render(doc, 80)
    }

    /// Start printing `signatures[sig]` (`tree_of_signature`).
    fn open_signature(&mut self, sig: u32, steps: &mut Vec<Step>) {
        let range = self.g.v.p.signatures[sig as usize];
        let saved_visible = self.visible;
        let hidden_start = self.hidden.len() as u32;
        let tail = self.signature_types.split_off(saved_visible as usize);
        self.hidden.extend(tail);
        self.frames.push(SigFrame {
            next: range.start,
            end: range.start + range.len,
            saved_visible,
            hidden_start,
            items_start: self.items.len() as u32,
            in_group: false,
        });
        steps.push(Step::Next);
    }

    /// One item of the innermost signature, or its end.
    fn next_item(&mut self, steps: &mut Vec<Step>) {
        let frame = self.frames.last_mut().expect("a signature frame");
        if frame.next == frame.end {
            let frame = self.frames.pop().expect("a signature frame");
            self.signature_types.truncate(frame.saved_visible as usize);
            let hidden = self.hidden.split_off(frame.hidden_start as usize);
            self.signature_types.extend(hidden);
            self.visible = frame.saved_visible;
            let mty = self.signature_doc(frame.items_start);
            self.mtys.push(mty);
            return;
        }
        let index = frame.next;
        frame.next += 1;
        let item = self.g.v.p.ordered_items[index as usize];
        let status = match item.status {
            ItemStatus::Recursive(RecStatus::First) => 1,
            ItemStatus::Recursive(RecStatus::Next) => 2,
            ItemStatus::Extension(ExtensionStatus::First) => 0,
            ItemStatus::Extension(ExtensionStatus::Next) => 1,
            ItemStatus::Extension(ExtensionStatus::Exception) => 2,
            _ => 0,
        };
        let frame = self.frames.last_mut().expect("a signature frame");
        frame.in_group = match (frame.in_group, item.kind, item.status) {
            (true, SignatureKind::Type, ItemStatus::Recursive(RecStatus::Next)) => true,
            (_, SignatureKind::Type, _) => {
                self.visible = self.signature_types.len() as u32;
                true
            }
            _ => {
                self.visible = self.signature_types.len() as u32;
                false
            }
        };
        steps.push(Step::Next);
        match item.kind {
            SignatureKind::Value => {
                let name = self.str(self.g.v.ident(item.ident).name);
                let doc = self.value(name, item.declaration);
                self.items.push(SigOut::Doc(doc));
            }
            SignatureKind::Type => {
                let name = self.g.v.ident(item.ident).name;
                if !is_row_name(self.str(name)) {
                    let doc = self.type_declaration(item.ident, item.declaration, status);
                    self.items.push(SigOut::Doc(doc));
                }
                self.signature_types.push(name);
            }
            SignatureKind::Extension => {
                let out = self.extension(item.ident, item.declaration, status);
                self.items.push(out);
            }
            SignatureKind::Module => {
                let module = self.g.v.p.modules[item.declaration as usize];
                let p = self.g.v.p;
                let attrs = &p.attributes[module.attributes.start as usize
                    ..(module.attributes.start + module.attributes.len) as usize];
                let ellipsis = attrs.iter().any(|attr| {
                    self.g.v.str(attr.name) == "..."
                        && matches!(
                            p.attribute_payloads[attr.payload as usize],
                            AttributePayloadRow::Empty
                        )
                });
                let name = self.g.v.ident(item.ident).name;
                // A submodule of a persistent unit is qualified by the unit's path.
                self.prefixes.push(name);
                steps.push(Step::Module {
                    name,
                    status,
                    scoped: true,
                });
                steps.push(Step::Mty {
                    row: module.module_type,
                    ellipsis,
                });
            }
            SignatureKind::ModuleType => {
                let module = self.g.v.p.modules[item.declaration as usize];
                let name = self.g.v.ident(item.ident).name;
                if module.module_type == NONE {
                    let text = format!("module type {} = ", self.str(name));
                    let head = self.docs.text(&text);
                    let nil = self.docs.nil();
                    let all = self.docs.concat(&[head, nil]);
                    let doc = self.docs.group(all);
                    self.items.push(SigOut::Doc(doc));
                } else {
                    steps.push(Step::ModuleTypeDecl { name });
                    steps.push(Step::Mty {
                        row: module.module_type,
                        ellipsis: false,
                    });
                }
            }
            SignatureKind::Class | SignatureKind::ClassType => {
                let doc = self.docs.nil();
                self.items.push(SigOut::Doc(doc));
            }
        }
    }

    /// `tree_of_modtype ~ellipsis`: a module type, onto `mtys` (a signature
    /// or functor is queued).
    fn module_type(&mut self, row: u32, ellipsis: bool, steps: &mut Vec<Step>) {
        match self.g.v.p.module_types[row as usize] {
            ModuleTypeRow::Ident(path) => {
                let doc = self.ident_doc(path, false, true);
                self.mtys.push(Mty::Plain(doc));
            }
            ModuleTypeRow::Alias { path, .. } => {
                let doc = self.ident_doc(path, false, true);
                self.mtys.push(Mty::Alias(doc));
            }
            ModuleTypeRow::Signature(sig) => {
                if ellipsis {
                    let start = self.items.len() as u32;
                    let dots = self.text("...");
                    self.items.push(SigOut::Doc(dots));
                    let mty = self.signature_doc(start);
                    self.mtys.push(mty);
                } else {
                    self.open_signature(sig, steps);
                }
            }
            ModuleTypeRow::Functor {
                parameter,
                parameter_type,
                result,
            } => {
                let has_type = parameter_type != NONE;
                steps.push(Step::Functor {
                    param: parameter,
                    has_type,
                });
                if has_type {
                    steps.push(Step::Mty {
                        row: parameter_type,
                        ellipsis: false,
                    });
                }
                steps.push(Step::Mty {
                    row: result,
                    ellipsis,
                });
            }
        }
    }

    /// `print_out_signature_doc` of the items from `start`, as a module type.
    fn signature_doc(&mut self, start: u32) -> Mty {
        let items: Vec<SigOut> = self.items.split_off(start as usize);
        if items.is_empty() {
            return Mty::EmptySignature;
        }
        let mut docs: smallvec::SmallVec<[D; 16]> = smallvec::SmallVec::new();
        let mut index = 0;
        while index < items.len() {
            match items[index] {
                SigOut::Ext {
                    constructor,
                    header,
                    status: 0,
                    private,
                } => {
                    // Gather the extension constructors that follow.
                    let mut constructors: smallvec::SmallVec<[D; 8]> =
                        smallvec::smallvec![constructor];
                    index += 1;
                    while let Some(SigOut::Ext {
                        constructor,
                        status: 1,
                        ..
                    }) = items.get(index)
                    {
                        constructors.push(*constructor);
                        index += 1;
                    }
                    let type_ = self.text("type ");
                    let plus = self.text(" += ");
                    let private = if private {
                        self.text("private ")
                    } else {
                        self.docs.nil()
                    };
                    let body = self.constructors_doc(&constructors);
                    let all = self.docs.concat(&[type_, header, plus, private, body]);
                    docs.push(self.docs.group(all));
                }
                SigOut::Ext {
                    constructor,
                    header,
                    private,
                    ..
                } => {
                    let type_ = self.text("type ");
                    let plus = self.text(" +=");
                    let line = self.docs.line();
                    let private = if private {
                        self.text("private ")
                    } else {
                        self.docs.nil()
                    };
                    let all = self
                        .docs
                        .concat(&[type_, header, plus, line, private, constructor]);
                    docs.push(self.docs.group(all));
                    index += 1;
                }
                SigOut::Doc(doc) => {
                    docs.push(doc);
                    index += 1;
                }
            }
        }
        let body = if docs.len() == 1 {
            docs[0]
        } else {
            let line = self.docs.line();
            let joined = self.docs.join(line, &docs);
            self.docs.breakable_group(joined, true)
        };
        let open = self.text("{");
        let line = self.docs.line();
        let inner = self.docs.concat(&[line, body]);
        let indented = self.docs.indent(inner);
        let soft = self.docs.soft_line();
        let close = self.text("}");
        let all = self.docs.concat(&[open, indented, soft, close]);
        Mty::Signature(self.docs.breakable_group(all, true))
    }

    /// `print_out_module_type_doc`.
    fn mty_doc(&mut self, mty: Mty) -> D {
        match mty {
            Mty::Alias(_) | Mty::EmptySignature => self.docs.nil(),
            Mty::Plain(doc) | Mty::Signature(doc) => doc,
            Mty::Functor { params, result } => {
                let mut list: smallvec::SmallVec<[FunctorParam; 4]> = smallvec::SmallVec::new();
                let mut current = params;
                while current != NONE {
                    let param = self.functor_params[current as usize];
                    list.push(param);
                    current = param.next;
                }
                let args = if list.len() == 1 && list[0].arg.is_none() {
                    self.text("()")
                } else {
                    let mut parts: smallvec::SmallVec<[D; 4]> = smallvec::SmallVec::new();
                    for param in &list {
                        let name = self.str(param.name);
                        let name = self.docs.text(name);
                        let arg = match param.arg {
                            None => self.docs.nil(),
                            Some(arg) => {
                                let colon = self.text(": ");
                                self.docs.concat(&[colon, arg])
                            }
                        };
                        let all = self.docs.concat(&[name, arg]);
                        parts.push(self.docs.group(all));
                    }
                    self.list_doc("(", &parts, ")")
                };
                let arrow = self.text(" => ");
                let all = self.docs.concat(&[args, arrow, result]);
                self.docs.group(all)
            }
        }
    }
}

/// O(1): `name` without its `#row` suffix when `trim`.
fn trim_row(name: &str, trim: bool) -> &str {
    if trim { &name[..name.len() - 4] } else { name }
}

/// O(length): `is_class_path` (variant_layout.rs:85): dot-separated
/// identifiers, the first not a JavaScript keyword.
fn is_class_path(name: &str) -> bool {
    fn is_start(c: u8) -> bool {
        c.is_ascii_alphabetic() || c == b'_' || c == b'$'
    }
    fn is_identifier(segment: &str) -> bool {
        let bytes = segment.as_bytes();
        !bytes.is_empty()
            && is_start(bytes[0])
            && bytes.iter().all(|c| c.is_ascii_digit() || is_start(*c))
    }
    let mut segments = name.split('.');
    match segments.next() {
        Some(global) => {
            is_identifier(global)
                && !crate::js_ir::printer::is_js_keyword(global)
                && segments.all(is_identifier)
        }
        None => false,
    }
}

/// O(length): `unsupported_class name = None` (variant_layout.rs:62).
fn supported_class(name: &str) -> bool {
    let mut segments = name.split('.');
    let first = segments.next().unwrap_or("");
    let more = segments.next().is_some();
    if first == "globalThis" && more {
        return false;
    }
    if more {
        return true;
    }
    !matches!(
        first,
        "Object"
            | "Function"
            | "Array"
            | "String"
            | "Number"
            | "Boolean"
            | "BigInt"
            | "Symbol"
            | "globalThis"
            | "undefined"
            | "NaN"
            | "Infinity"
            | "Math"
            | "JSON"
            | "Reflect"
            | "Atomics"
            | "Intl"
            | "Proxy"
    )
}

#[cfg(test)]
mod tests {
    #[test]
    fn work_item_sizes() {
        assert!(std::mem::size_of::<super::Task>() <= 16);
        assert_eq!(std::mem::size_of::<super::Step>(), 8);
        assert_eq!(std::mem::size_of::<super::Out>(), 12);
        assert_eq!(std::mem::size_of::<super::Mty>(), 12);
        assert_eq!(std::mem::size_of::<super::SigOut>(), 12);
        assert_eq!(std::mem::size_of::<super::PolyFrame>(), 24);
        assert_eq!(std::mem::size_of::<super::FunctorParam>(), 16);
    }
}
