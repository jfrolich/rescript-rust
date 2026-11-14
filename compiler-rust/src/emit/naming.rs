//! Printed identifier assignment (legacy `JsPrinter`, and
//! compiler/ext/ext_pp_scope.ml: add_ident, merge, sub_scope).
//!
//! There are program and function naming scopes only. Blocks, loops and catches
//! continue their containing scope (loop/catch binders precede their children).
//! Imports precede program reservations, statements, then exports. Declarations
//! name the binder before the initializer, except non-eta functions: their free
//! identifiers plus the binder are reserved first, sorted by Ident's order.
//! Eta declarations name the binder first, then reserve the same environment.
//! Function parameters precede their printed body. Omitted declarations/branches
//! and eta-reduced bodies do not assign names, but still affect free variables.
//!
//! A visible identifier keeps its spelling. Otherwise convert_ident_atom mangles
//! punctuation and prefixes reserved words/known JS globals with `$$`; the
//! current scope assigns base, base$1, ...,
//! starting at that base's next unused suffix. Candidates already used by ANY
//! base are skipped; suffixed candidates also skip raw JS names in the program.
//! Stamp-zero uses print their raw name, but function environments reserve their
//! converted base with stamp zero. Module identifiers always use converted names.
//! Exports use the local assigned name; their public spelling is js_export_name
//! (the same conversion except that exported `default` stays `default`),
//! independently of suffixes. External shadow renaming remains an earlier pass.
//!
//! Function entry reserves its environment in the parent, then inherits the
//! ENTIRE suffix table of each environment base, not all enclosing bases. The
//! visible-ident index still includes ancestors. Function exit restores that
//! index; siblings do not inherit each other's local assignments.
//!
//! Costs: visible lookup is one expected O(1) hash lookup, never a scope-chain
//! search. Entry costs O(environment identifiers); exit costs O(inherited bases
//! plus assignments made in that scope).
//! Suffix tables are persistent HAMTs (bounded depth for machine-word hashes),
//! so entry shares them without copying stamps. A candidate can belong to only
//! two tables: its literal base, or the prefix before a final canonical $number.
//! Thus used-name checks need at most two table lookups, not a union or scan.
//! Names are interned; uses never allocate Strings. Suffix allocation pays for
//! the spelling only once, per new assignment.
//!
//! Explicit free environments can themselves be quadratic in tree size. A work
//! budget proportional to the input bounds environment propagation, sorting and
//! suffix probes; exceeding it falls back as `scoped naming work budget`, rather
//! than doing quadratic work. Supported inputs therefore take expected linear
//! work in nodes/identifier occurrences/scopes (plus identifier spelling bytes).
//! The deep-nesting test counts this work, including environment preparation.
use super::{Unsupported, walk};
use crate::ident::Ident;
use crate::js_ir::printer::convert_ident_atom;
use crate::js_ir::walk::{Visitor, walk_block};
use crate::js_ir::{
    ModulePathResolver,
    arena::{Expr, ExprKind, FunId, JsArena, JsDepsProgram, Stmt, StmtKind},
};
use crate::name::Name;
use ahash::{AHashMap as HashMap, AHashSet as HashSet};

#[derive(Clone, Default)]
struct Group {
    next: usize,
    stamps: im_rc::HashMap<i32, Name>,
    used: im_rc::HashSet<Name>,
}
#[derive(Default)]
struct Scope {
    groups: HashMap<Name, Group>,
    assigned: Vec<Ident>,
    previous_groups: Vec<(Name, Option<usize>)>,
}
#[derive(Default)]
pub(super) struct Names {
    printed: HashMap<Ident, Name>,
    finishes: HashMap<Stmt, Name>,
    visible: HashMap<Ident, Name>,
    visible_groups: HashMap<Name, usize>,
    scopes: Vec<Scope>,
    raw: HashSet<Name>,
    converted: HashMap<Name, Name>,
    free: HashMap<FunId, Vec<Ident>>,
    method_this: HashSet<FunId>,
    jsx_preserve: bool,
    string_tasks: Vec<Expr>,
    steps: usize,
    budget: usize,
}
impl Names {
    pub(super) fn method_this_used(&self, f: FunId) -> bool {
        self.method_this.contains(&f)
    }

    fn string_leaves(
        &mut self,
        a: &JsArena,
        root: Expr,
        mut visit: impl FnMut(&mut Self, Expr) -> Result<(), Unsupported>,
    ) -> Result<(), Unsupported> {
        let mut scratch = std::mem::take(&mut self.string_tasks);
        let result = walk::string_leaves(a, root, &mut scratch, |e| visit(self, e));
        scratch.clear();
        self.string_tasks = scratch;
        result
    }
    fn charge(&mut self, n: usize) -> Result<(), Unsupported> {
        self.steps = self.steps.saturating_add(n);
        if self.steps > self.budget {
            Err(Unsupported("scoped naming work budget"))
        } else {
            Ok(())
        }
    }
    pub(super) fn get(&self, id: &Ident) -> &str {
        &self.printed[id]
    }

    pub(super) fn finish(&self, s: Stmt) -> &str {
        &self.finishes[&s]
    }

    /// A hole prefix longer than every printed name starting with the reserved
    /// stem cannot collide with any local, global, import, or loop-finish name.
    pub(super) fn raw_prefix_len(&self) -> usize {
        self.printed
            .values()
            .chain(self.finishes.values())
            .filter(|n| n.starts_with(super::raw::PREFIX))
            .map(|n| n.len() + 1)
            .max()
            .unwrap_or(super::raw::PREFIX.len())
    }

    fn base(&mut self, id: Ident) -> Name {
        *self
            .converted
            .entry(id.name_atom())
            .or_insert_with(|| convert_ident_atom(id.name_atom()))
    }

    fn used(&self, name: Name) -> bool {
        let groups = &self.scopes.last().unwrap().groups;
        if groups.get(&name).is_some_and(|g| g.used.contains(&name)) {
            return true;
        }
        // A suffix is always a positive decimal integer without leading zeros.
        if let Some((base, suffix)) = name.rsplit_once('$')
            && suffix.starts_with(|c: char| ('1'..='9').contains(&c))
            && suffix.bytes().all(|c| c.is_ascii_digit())
        {
            return groups
                .get(&Name::new(base))
                .is_some_and(|g| g.used.contains(&name));
        }
        false
    }
    fn assign(&mut self, base: Name, stamp: i32) -> Result<Name, Unsupported> {
        self.charge(1)?;
        let scope = self.scopes.last().unwrap();
        if let Some(n) = scope.groups.get(&base).and_then(|g| g.stamps.get(&stamp)) {
            return Ok(*n);
        }
        let mut next = scope.groups.get(&base).map_or(0, |g| g.next);
        let name = loop {
            self.charge(1)?;
            let name = if next == 0 {
                base
            } else {
                Name::new(&format!("{base}${next}"))
            };
            if !self.used(name) && !(next > 0 && self.raw.contains(&name)) {
                break name;
            }
            next += 1;
        };
        let index = self.scopes.len() - 1;
        if !self.scopes[index].groups.contains_key(&base) {
            let old = self.visible_groups.insert(base, index);
            self.scopes[index].previous_groups.push((base, old));
        }
        let group = self.scopes[index].groups.entry(base).or_default();
        group.next = next + 1;
        group.stamps.insert(stamp, name);
        group.used.insert(name);
        Ok(name)
    }
    fn remember(&mut self, id: Ident, name: Name) -> Result<(), Unsupported> {
        if let Some(old) = self.printed.insert(id, name)
            && old != name
        {
            // The builder currently indexes names by Ident, not by occurrence.
            return Err(Unsupported(
                "identifier spelling differs between sibling scopes",
            ));
        }
        Ok(())
    }
    fn add(&mut self, id: Ident, module: bool) -> Result<(), Unsupported> {
        self.charge(1)?;
        let name = if let Some(name) = self.visible.get(&id) {
            *name
        } else if id.stamp() == 0 && !module {
            id.name_atom()
        } else {
            let base = self.base(id);
            let name = self.assign(base, id.stamp())?;
            self.visible.insert(id, name);
            self.scopes.last_mut().unwrap().assigned.push(id);
            name
        };
        self.remember(id, name)
    }
    fn reserve(&mut self, ids: &[Ident]) -> Result<(), Unsupported> {
        for id in ids {
            if id.stamp() == 0 {
                let base = self.base(*id);
                self.assign(base, 0)?;
            } else {
                self.add(*id, false)?;
            }
        }
        Ok(())
    }
    fn enter(&mut self, ids: &[Ident]) -> Result<(), Unsupported> {
        self.reserve(ids)?;
        let mut inner = Scope::default();
        for id in ids {
            self.charge(1)?;
            let base = self.base(*id);
            if inner.groups.contains_key(&base) {
                continue;
            }
            // A visible identifier may have been named in an ancestor rather
            // than the immediate parent. Its inherited table is tracked below.
            let index = self.visible_groups[&base];
            inner
                .groups
                .insert(base, self.scopes[index].groups[&base].clone());
        }
        for base in inner.groups.keys() {
            let old = self.visible_groups.insert(*base, self.scopes.len());
            inner.previous_groups.push((*base, old));
        }
        self.scopes.push(inner);
        Ok(())
    }
    fn leave(&mut self) {
        let scope = self.scopes.pop().unwrap();
        for id in scope.assigned {
            self.visible.remove(&id);
        }
        for (base, previous) in scope.previous_groups {
            match previous {
                Some(index) => {
                    self.visible_groups.insert(base, index);
                }
                None => {
                    self.visible_groups.remove(&base);
                }
            }
        }
    }
    pub(super) fn collect(
        p: &JsDepsProgram,
        resolver: &ModulePathResolver,
        jsx_preserve: bool,
    ) -> Result<Self, Unsupported> {
        #[derive(Default)]
        struct Input {
            count: usize,
            raw: HashSet<Name>,
            strings: Vec<Expr>,
        }
        impl Visitor for Input {
            fn visit_string_children(&mut self, a: &JsArena, left: Expr, right: Expr) -> bool {
                let mut pending = std::mem::take(&mut self.strings);
                pending.extend([right, left]);
                while let Some(e) = pending.pop() {
                    if let Some((l, r)) = walk::string_children(a, e) {
                        self.visit_expression(a, e);
                        pending.extend([r, l]);
                    } else {
                        crate::js_ir::walk::walk_expression(self, a, e);
                    }
                }
                self.strings = pending;
                true
            }
            fn visit_expression(&mut self, a: &JsArena, e: Expr) {
                self.count += 1;
                if let ExprKind::Var(id) = a.ek(e)
                    && crate::js_ir::arena::is_raw_js_name(&a.ident(id))
                {
                    self.raw.insert(a.ident(id).name_atom());
                }
                if let ExprKind::Fun(f) = a.ek(e) {
                    for id in a.ident_slice(a.fun(f).params) {
                        self.count += 1;
                        if crate::js_ir::arena::is_raw_js_name(id) {
                            self.raw.insert(id.name_atom());
                        }
                    }
                }
            }
            fn visit_declaration(&mut self, _a: &JsArena, d: &crate::js_ir::arena::VarDecl) {
                self.count += 1;
                if crate::js_ir::arena::is_raw_js_name(&d.ident) {
                    self.raw.insert(d.ident.name_atom());
                }
            }
            fn visit_block(&mut self, _a: &JsArena, b: &[Stmt]) {
                self.count += b.len();
            }
        }
        let a = &p.program.arena;
        let mut input = Input::default();
        walk_block(&mut input, a, &p.program.block);
        let mut names = Self {
            jsx_preserve,
            budget: 64
                * (input.count
                    + p.modules.len()
                    + p.program.name_reservations.len()
                    + p.program.exports.len()
                    + 1),
            raw: input.raw,
            scopes: vec![Scope::default()],
            ..Self::default()
        };
        // Analyze unprinted children too, as the legacy environment pass does.
        names.analyze_block(
            a,
            &p.program.block,
            &mut HashSet::new(),
            &mut HashSet::new(),
        )?;
        for module in &p.modules {
            if !module.dynamic_import && resolver.resolve_module_path(module).is_some() {
                names.add(module.id, true)?;
            }
        }
        names.reserve(&p.program.name_reservations)?;
        names.block(a, &p.program.block, true, None)?;
        for id in &p.program.exports {
            names.add(*id, false)?;
        }
        Ok(names)
    }
    fn sorted(&mut self, ids: HashSet<Ident>) -> Result<Vec<Ident>, Unsupported> {
        self.charge(ids.len() * (ids.len().max(1).ilog2() as usize + 1))?;
        let mut ids: Vec<_> = ids.into_iter().collect();
        ids.sort();
        Ok(ids)
    }
    fn analyze_fun(&mut self, a: &JsArena, f: FunId) -> Result<(), Unsupported> {
        if self.free.contains_key(&f) {
            return Ok(());
        }
        let info = a.fun(f);
        let params = a.ident_slice(info.params);
        let mut defined: HashSet<_> = params
            .iter()
            .skip(usize::from(info.is_method))
            .copied()
            .collect();
        let mut used = HashSet::new();
        self.analyze_block(a, a.stmts(info.body), &mut defined, &mut used)?;
        self.charge(used.len() + defined.len())?;
        used.retain(|id| !defined.contains(id));
        if info.is_method
            && let Some(this) = params.first()
            && used.remove(this)
        {
            self.method_this.insert(f);
        }
        let ids = self.sorted(used)?;
        self.free.insert(f, ids);
        Ok(())
    }
    fn analyze_expr(
        &mut self,
        a: &JsArena,
        e: Expr,
        defined: &mut HashSet<Ident>,
        used: &mut HashSet<Ident>,
    ) -> Result<(), Unsupported> {
        self.charge(1)?;
        walk::expression_comment(a, e)?;
        match a.ek(e) {
            ExprKind::Var(id) => {
                let id = a.ident(id);
                if !defined.contains(&id) {
                    used.insert(id);
                }
            }
            ExprKind::Qualified(q) => {
                let id = a.qual(q).0.id;
                if !defined.contains(&id) {
                    used.insert(id);
                }
            }
            ExprKind::Fun(f) => {
                self.analyze_fun(a, f)?;
                self.charge(self.free[&f].len())?;
                used.extend(self.free[&f].iter().copied());
            }
            ExprKind::CamlBlock(items, _, tag) => {
                let (items, tag) = (a.exprs(items), a.tag(tag));
                walk::block_supported(items, tag)?;
                for (_, e) in walk::block_elements(a, items, tag) {
                    self.analyze_expr(a, e, defined, used)?;
                }
                // printer::collect_expression_idents visits even malformed
                // PolyVar payloads beyond the printed NAME/VAL pair.
                if matches!(tag, crate::lambda::TagInfo::PolyVar(_)) {
                    for &e in items.iter().skip(2) {
                        self.analyze_expr(a, e, defined, used)?;
                    }
                }
            }
            ExprKind::StringAppend(..) => {
                self.string_leaves(a, e, |this, e| this.analyze_expr(a, e, defined, used))?
            }
            _ => children(a, e, self.jsx_preserve, |e| {
                self.analyze_expr(a, e, defined, used)
            })?,
        }
        Ok(())
    }
    fn analyze_block(
        &mut self,
        a: &JsArena,
        block: &[Stmt],
        defined: &mut HashSet<Ident>,
        used: &mut HashSet<Ident>,
    ) -> Result<(), Unsupported> {
        for s in block {
            self.charge(1)?;
            match a.sk(*s) {
                StmtKind::Block(b) => self.analyze_block(a, a.stmts(b), defined, used)?,
                StmtKind::Variable(v) => {
                    let d = a.var(v);
                    if let Some((fields, _)) = walk::rest_declaration(a, d) {
                        for field in a.rest(fields) {
                            if let Some(id) = field.ident {
                                defined.insert(id);
                            }
                        }
                    }
                    defined.insert(d.ident);
                    if let Some(e) = d.value {
                        self.analyze_expr(a, e, defined, used)?;
                    }
                }
                StmtKind::Exp(e) | StmtKind::Return(e) => self.analyze_expr(a, e, defined, used)?,
                StmtKind::If(c, t, f) => {
                    self.analyze_expr(a, c, defined, used)?;
                    self.analyze_block(a, a.stmts(t), defined, used)?;
                    self.analyze_block(a, a.stmts(f), defined, used)?;
                }
                StmtKind::Debugger => {}
                _ => walk::statement_children(a, *s, |child| {
                    match child {
                        walk::StatementChild::Binder(id) => {
                            defined.insert(id);
                        }
                        walk::StatementChild::Finish(_) => {}
                        walk::StatementChild::Expression(e) => {
                            self.analyze_expr(a, e, defined, used)?
                        }
                        walk::StatementChild::Block(b) => {
                            self.analyze_block(a, a.stmts(b), defined, used)?
                        }
                    }
                    Ok(())
                })?,
            }
        }
        Ok(())
    }
    fn function(
        &mut self,
        a: &JsArena,
        f: FunId,
        binding: Option<Ident>,
        top: bool,
    ) -> Result<(), Unsupported> {
        let form = walk::function_form(a, f, top)?;
        self.charge(self.free[&f].len())?;
        let mut ids = self.free[&f].clone();
        if let Some(id) = binding {
            if matches!(form, walk::FunctionForm::Eta(_)) {
                self.add(id, false)?;
            }
            if let Err(pos) = ids.binary_search(&id) {
                ids.insert(pos, id);
            }
        }
        self.reserve(&ids)?;
        if let Some(id) = binding {
            self.add(id, false)?;
        }
        self.enter(&ids)?;
        let info = a.fun(f);
        match form {
            walk::FunctionForm::Eta(e) => self.expr(a, e)?,
            _ => {
                for (i, id) in a.ident_slice(info.params).iter().enumerate() {
                    if info.is_method && i == 0 && !self.method_this_used(f) {
                        continue;
                    }
                    self.add(*id, false)?;
                }
                match form {
                    walk::FunctionForm::ArrowExpression(e) => self.expr(a, e)?,
                    walk::FunctionForm::ArrowEmpty => {}
                    _ => self.block(
                        a,
                        walk::function_body(a, a.stmts(info.body)),
                        false,
                        Some(info.return_unit),
                    )?,
                }
            }
        }
        self.leave();
        Ok(())
    }
    fn expr(&mut self, a: &JsArena, e: Expr) -> Result<(), Unsupported> {
        self.charge(1)?;
        // collect analyzes the entire immutable arena before assigning names;
        // analyze_expr already validated these comments, including unprinted
        // children. The standalone AST builder retains its own validation.
        match a.ek(e) {
            ExprKind::Var(id) => self.add(a.ident(id), false),
            ExprKind::Qualified(q) => self.add(a.qual(q).0.id, true),
            ExprKind::Fun(f) => self.function(a, f, None, false),
            ExprKind::StringAppend(..) => self.string_leaves(a, e, |this, e| this.expr(a, e)),
            _ => children(a, e, self.jsx_preserve, |e| self.expr(a, e)),
        }
    }
    fn block(
        &mut self,
        a: &JsArena,
        b: &[Stmt],
        top: bool,
        tail: Option<bool>,
    ) -> Result<(), Unsupported> {
        for (i, s) in b.iter().enumerate() {
            self.stmt(a, *s, top, if i + 1 == b.len() { tail } else { None })?;
        }
        Ok(())
    }
    fn stmt(
        &mut self,
        a: &JsArena,
        s: Stmt,
        top: bool,
        tail: Option<bool>,
    ) -> Result<(), Unsupported> {
        self.charge(1)?;
        match a.sk(s) {
            StmtKind::Block(b) => self.block(a, a.stmts(b), false, None)?,
            StmtKind::Variable(v) => {
                let d = a.var(v);
                match walk::prints_declaration(d) {
                    walk::Declaration::Omit => return Ok(()),
                    walk::Declaration::Effect(e) => {
                        return if walk::omitted_expression(a, e) {
                            Ok(())
                        } else {
                            self.expr(a, e)
                        };
                    }
                    walk::Declaration::Binding => {}
                }
                if let Some(e) = d.value
                    && let ExprKind::Fun(f) = a.ek(e)
                {
                    return self.function(a, f, Some(d.ident), top);
                }
                if let Some((fields, _)) = walk::rest_declaration(a, d) {
                    for field in a.rest(fields) {
                        if let Some(id) = field.ident {
                            self.add(id, false)?;
                        }
                    }
                }
                self.add(d.ident, false)?;
                if let Some(e) = d.value
                    && !walk::undefined(a, e)
                {
                    self.expr(a, e)?;
                }
            }
            StmtKind::Exp(e) => {
                if !walk::omitted_expression(a, e) {
                    self.expr(a, e)?;
                }
            }
            StmtKind::Return(e) if tail == Some(true) => {
                if let Some(e) = walk::tail_effect(a, e) {
                    self.expr(a, e)?;
                }
            }
            StmtKind::Return(e) => {
                if !walk::undefined(a, e) {
                    self.expr(a, e)?;
                }
            }
            StmtKind::If(c, t, f) => {
                self.expr(a, c)?;
                self.block(a, a.stmts(t), false, None)?;
                let f = a.stmts(f);
                if !walk::else_omitted(a, f)
                    && !(tail.is_some() && matches!(f,[s] if walk::return_undefined(a,*s)))
                {
                    if let Some(s) = walk::else_if(a, f) {
                        self.stmt(a, s, false, None)?;
                    } else {
                        self.block(a, f, false, None)?;
                    }
                }
            }
            StmtKind::Debugger => {}
            _ => walk::statement_children(a, s, |child| {
                match child {
                    walk::StatementChild::Binder(id) => self.add(id, false)?,
                    walk::StatementChild::Finish(s) => {
                        let StmtKind::ForRange(id) = a.sk(s) else {
                            unreachable!()
                        };
                        let base = self.base(a.ident(a.for_range(id).ident));
                        let stamp = -1 - self.finishes.len() as i32;
                        let name = self.assign(Name::new(&format!("{base}_finish")), stamp)?;
                        if self.finishes.insert(s, name).is_some_and(|old| old != name) {
                            return Err(Unsupported(
                                "range finish spelling differs between occurrences",
                            ));
                        }
                    }
                    walk::StatementChild::Expression(e) => self.expr(a, e)?,
                    walk::StatementChild::Block(b) => self.block(a, a.stmts(b), false, None)?,
                }
                Ok(())
            })?,
        }
        Ok(())
    }
}

/// One identifier handed to the naming tables: where its name is kept and
/// what `Ident`'s order and the suffix rule read of it. `slot` is dense per
/// unit: the index of the variable an identifier prints as (its origin), or
/// the number of variables plus the index of an imported module. Two slots
/// whose identifiers have one nonzero stamp would get one name in the pass,
/// which keys names by `Ident` (equal when the nonzero stamps are equal,
/// `Ident::same`), and two names here, which key them by slot. That does
/// not occur: a positive stamp is created for one identifier only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Subject {
    pub(crate) slot: u32,
    pub(crate) stamp: i32,
    pub(crate) name: Name,
}

/// The suffix table of one base (the pass's `Group`), as it stands in the
/// scope that is current. `scope` is the depth of the scope that created or
/// inherited it: the group exists in the current scope only when that is
/// the current depth, otherwise it reads as empty. A name `base$k` of this
/// base is taken when the group exists, `k < next` and `(group, k)` is not
/// in `Tables::skipped`; `k` zero is the base itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct GroupRow {
    next: u32,
    scope: u32,
    /// The name reserved for stamp zero (`Names::reserve`), if any.
    zero: Option<Name>,
}

/// A group row as it was before the current scope changed it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Saved {
    group: u32,
    row: GroupRow,
}

/// Where the current scope's part of each undo stack starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Level {
    saved: u32,
    assigned: u32,
    skipped: u32,
}

/// The naming rule of this file's header on dense tables with an undo
/// stack, for the replay of the naming log (THREE_TREES 11.4, "T5 part B as
/// redesigned"): no persistent map, so entering a function and assigning in
/// an inherited group allocate nothing. The pass's `Names` stays as it is
/// and is the oracle (`compare_with_pass`).
///
/// A scope is a level. A group is inherited by re-tagging its row with the
/// new depth (the row before is saved); a group the scope does not inherit
/// keeps its old tag and so reads as empty until the scope assigns in it
/// (the row before is saved, then reset). `leave` restores the saved rows
/// last to first, forgets the names assigned in the scope and truncates the
/// skipped candidates.
#[derive(Default)]
pub(crate) struct Tables {
    groups: Vec<GroupRow>,
    /// The group of each converted base. A hash map: the key is a spelling
    /// that several variables share and that has no index of its own; it is
    /// read once per slot, never per event (`slot_group` keeps the answer).
    bases: HashMap<Name, u32>,
    /// The group of each slot plus one, zero while unknown. Dense by slot.
    slot_group: Vec<u32>,
    /// The name of each slot while a scope on the stack has it assigned
    /// (the pass's `visible`). Dense by slot.
    visible: Vec<Option<Name>>,
    saved: Vec<Saved>,
    /// The slots named in the scopes on the stack, innermost last.
    assigned: Vec<u32>,
    /// `(group, suffix)` of each candidate that was passed over because
    /// another base or a raw name has that spelling.
    skipped: Vec<[u32; 2]>,
    levels: Vec<Level>,
    /// The raw JavaScript names of the unit. A hash set for the reason
    /// `bases` is a hash map; read only for a suffixed candidate.
    raw: HashSet<Name>,
    /// The spelling of a suffixed candidate, reused.
    spelling: String,
    /// Synthetic names handed out (`Names::finishes`).
    synthetic: u32,
    /// What the suffix rule reads of each group besides its row. Dense by
    /// group.
    marks: Vec<Marks>,
    /// `Marks::born` of the row each entry of `saved` holds. Parallel to
    /// `saved`.
    saved_born: Vec<u32>,
    /// Per entry of `skipped`: the group whose `Marks::zero_skip` (for
    /// suffix zero) or `Marks::as_skip` (otherwise) the entry replaced,
    /// `NONE` when it replaced none, and the value it replaced.
    skip_undo: Vec<[u32; 2]>,
    /// One per call of `add`, `add_module`, `reserve` and `synthetic`, one
    /// per identifier of `enter`, one per candidate tried, one per entry
    /// undone by `leave` or `begin`.
    pub(crate) steps: usize,
}

/// No entry: an empty pointer of `Marks`, or no prefix group.
const NONE: u32 = u32::MAX;

/// What the suffix rule reads of one group besides its `GroupRow`.
#[derive(Clone, Copy)]
struct Marks {
    /// The base the group is the suffix table of.
    name: Name,
    /// The length of `Tables::skipped` when the current row was reset: an
    /// entry of this group's below it belongs to an older row.
    born: u32,
    /// The latest entry of `Tables::skipped` for `(this group, 0)`.
    zero_skip: u32,
    /// The latest entry of `Tables::skipped` whose candidate is spelled
    /// like this group's base: `(prefix, suffix)`.
    as_skip: u32,
    /// The group of the base before the final canonical `$number`, or
    /// `NONE`, and that number.
    prefix: u32,
    suffix: u32,
}

impl Tables {
    /// Empty the tables for a unit of `slots` slots without releasing their
    /// storage, with the program as the current scope. Cost: one step per
    /// group and per name of the previous unit, one per raw name.
    pub(crate) fn begin(&mut self, slots: usize, raw: &[Name]) {
        self.steps += self.groups.len() + self.assigned.len() + raw.len();
        self.groups.clear();
        self.marks.clear();
        self.bases.clear();
        self.slot_group.clear();
        self.slot_group.resize(slots, 0);
        self.visible.clear();
        self.visible.resize(slots, None);
        self.saved.clear();
        self.saved_born.clear();
        self.assigned.clear();
        self.skipped.clear();
        self.skip_undo.clear();
        self.levels.clear();
        self.levels.push(Level {
            saved: 0,
            assigned: 0,
            skipped: 0,
        });
        self.raw.clear();
        self.raw.extend(raw.iter().copied());
        self.spelling.clear();
        self.synthetic = 0;
    }

    /// `Names::add` for a variable: its visible name, or its own spelling
    /// for stamp zero, or a new name in the current scope (the converted
    /// base, then `base$1`, ... from the group's next suffix, skipping
    /// spellings taken by any base in the current scope and, for a suffixed
    /// candidate, raw names). Cost: one step, and for a new name: the first
    /// time the slot is named in the unit, one conversion and one `bases`
    /// lookup (one more for the prefix of a base new to the unit that ends
    /// in a canonical `$number`); one step per candidate tried; per suffixed
    /// candidate one interner lookup, one `bases` lookup and, when no base
    /// of the current scope has its spelling, one `raw` lookup; for the base
    /// itself one `raw` lookup when its prefix's group is in the current
    /// scope; one push to `assigned`, two pushes when the group is reset in
    /// this scope and two per candidate passed over.
    pub(crate) fn add(&mut self, subject: Subject) -> Name {
        self.steps += 1;
        if let Some(name) = self.visible[subject.slot as usize] {
            name
        } else if subject.stamp == 0 {
            subject.name
        } else {
            self.name_visible(subject)
        }
    }

    /// `Names::add` for an imported module: as `add`, but stamp zero is
    /// named like any other stamp. Cost: as `add`.
    pub(crate) fn add_module(&mut self, subject: Subject) -> Name {
        self.steps += 1;
        match self.visible[subject.slot as usize] {
            Some(name) => name,
            None => self.name_visible(subject),
        }
    }

    /// `Names::reserve` for one identifier: stamp zero reserves its
    /// converted base in the current scope without a visible name; any
    /// other is `add`. Returns whether a name was assigned that was not
    /// visible before. Cost: as `add`.
    pub(crate) fn reserve(&mut self, subject: Subject) -> bool {
        self.steps += 1;
        if subject.stamp == 0 {
            let group = self.slot_group(subject);
            self.assign(group, true);
            false
        } else if self.visible[subject.slot as usize].is_some() {
            false
        } else {
            self.name_visible(subject);
            true
        }
    }

    /// `Names::enter` without its reservation (the caller reserved): a new
    /// scope that inherits the group of each base of `environment` from the
    /// nearest scope that has it. Cost: one step and at most one push per
    /// identifier, one push for the level.
    pub(crate) fn enter(&mut self, environment: &[Subject]) {
        self.levels.push(Level {
            saved: self.saved.len() as u32,
            assigned: self.assigned.len() as u32,
            skipped: self.skipped.len() as u32,
        });
        let depth = self.depth();
        for subject in environment {
            self.steps += 1;
            let group = self.slot_group(*subject);
            // All tags are at most the depth: a row tagged below it is the
            // group of the nearest scope that has one, the one to inherit.
            if self.groups[group as usize].scope != depth {
                self.save(group);
                self.groups[group as usize].scope = depth;
            }
        }
    }

    /// `Names::leave`. Cost: one step per group row the scope changed, per
    /// name it assigned and per candidate it skipped.
    pub(crate) fn leave(&mut self) {
        let level = self.levels.pop().expect("a scope to leave");
        let skipped = level.skipped as usize;
        self.steps += self.skipped.len() - skipped;
        for (entry, [target, previous]) in self.skipped[skipped..]
            .iter()
            .zip(&self.skip_undo[skipped..])
            .rev()
        {
            if *target != NONE {
                let marks = &mut self.marks[*target as usize];
                if entry[1] == 0 {
                    marks.zero_skip = *previous;
                } else {
                    marks.as_skip = *previous;
                }
            }
        }
        self.skipped.truncate(skipped);
        self.skip_undo.truncate(skipped);
        let assigned = level.assigned as usize;
        self.steps += self.assigned.len() - assigned;
        for slot in self.assigned.drain(assigned..) {
            self.visible[slot as usize] = None;
        }
        let saved = level.saved as usize;
        self.steps += self.saved.len() - saved;
        for (entry, born) in self.saved[saved..]
            .iter()
            .zip(&self.saved_born[saved..])
            .rev()
        {
            self.groups[entry.group as usize] = entry.row;
            self.marks[entry.group as usize].born = *born;
        }
        self.saved.truncate(saved);
        self.saved_born.truncate(saved);
    }

    /// A name for something that is no identifier of the program (the
    /// cached bound of a range loop: `Names::finishes`): `base` under the
    /// suffix rule, in the current scope, with a stamp of its own. Cost: as
    /// a new name of `add`, without the visible entry.
    pub(crate) fn synthetic(&mut self, base: Name) -> Name {
        self.steps += 1;
        self.synthetic += 1;
        let group = self.group(base);
        self.assign(group, false)
    }

    /// The depth of the current scope; the program is zero.
    fn depth(&self) -> u32 {
        self.levels.len() as u32 - 1
    }

    /// A new name for a slot that has none visible, made visible in the
    /// current scope (the rest of `Names::add`). One push to `assigned`
    /// plus `assign`.
    fn name_visible(&mut self, subject: Subject) -> Name {
        let group = self.slot_group(subject);
        let name = self.assign(group, subject.stamp == 0);
        self.visible[subject.slot as usize] = Some(name);
        self.assigned.push(subject.slot);
        name
    }

    /// The group of the slot's converted base: `slot_group`, or one
    /// conversion and one hash lookup the first time.
    fn slot_group(&mut self, subject: Subject) -> u32 {
        let known = self.slot_group[subject.slot as usize];
        if known != 0 {
            return known - 1;
        }
        let group = self.group(convert_ident_atom(subject.name));
        self.slot_group[subject.slot as usize] = group + 1;
        group
    }

    /// The group of `base`, made with an empty row when there is none: one
    /// hash lookup, and for a new group whose base ends in a canonical
    /// `$number` the group of the part before it.
    fn group(&mut self, base: Name) -> u32 {
        if let Some(group) = self.bases.get(&base) {
            return *group;
        }
        let (prefix, suffix) = match canonical_suffix(base.as_str()) {
            Some((prefix, suffix)) => (self.group(Name::new(prefix)), suffix),
            None => (NONE, 0),
        };
        let group = self.groups.len() as u32;
        self.groups.push(GroupRow {
            next: 0,
            scope: 0,
            zero: None,
        });
        self.marks.push(Marks {
            name: base,
            born: 0,
            zero_skip: NONE,
            as_skip: NONE,
            prefix,
            suffix,
        });
        self.bases.insert(base, group);
        group
    }

    /// Push the row of `group` on the undo stack.
    fn save(&mut self, group: u32) {
        self.saved.push(Saved {
            group,
            row: self.groups[group as usize],
        });
        self.saved_born.push(self.marks[group as usize].born);
    }

    /// Whether `entry` of `skipped` is one of `group`'s current row.
    fn current_skip(&self, entry: u32, group: u32) -> bool {
        entry != NONE && entry >= self.marks[group as usize].born
    }

    /// Whether the base of `group` itself is taken in the current scope
    /// (`Names::used` of a name that is the base of its group).
    fn base_taken(&self, group: u32, depth: u32) -> bool {
        let row = self.groups[group as usize];
        row.scope == depth
            && row.next > 0
            && !self.current_skip(self.marks[group as usize].zero_skip, group)
    }

    /// The suffix rule of `Names::assign` on group `group` (the stamp-zero
    /// name returned if `zero` and the group has one): a group not in the
    /// current scope is reset first. One step per candidate.
    fn assign(&mut self, group: u32, zero: bool) -> Name {
        let depth = self.depth();
        let index = group as usize;
        if self.groups[index].scope != depth {
            self.save(group);
            self.groups[index] = GroupRow {
                next: 0,
                scope: depth,
                zero: None,
            };
            self.marks[index].born = self.skipped.len() as u32;
        }
        if zero && let Some(name) = self.groups[index].zero {
            return name;
        }
        let marks = self.marks[index];
        let mut next = self.groups[index].next;
        let name = loop {
            self.steps += 1;
            if next == 0 {
                // The base is taken by the group of its prefix when that
                // tried the same spelling as a suffix and kept it: tried
                // because the suffix is below its next, kept unless a raw
                // name or another base had it then.
                let prefix = marks.prefix;
                let taken = prefix != NONE && {
                    let row = self.groups[prefix as usize];
                    row.scope == depth
                        && marks.suffix < row.next
                        && !self.raw.contains(&marks.name)
                        && !self.current_skip(marks.as_skip, prefix)
                };
                if !taken {
                    break marks.name;
                }
                self.skip(group, 0, group);
            } else {
                self.spelling.clear();
                self.spelling.push_str(marks.name.as_str());
                self.spelling.push('$');
                push_decimal(&mut self.spelling, next);
                let candidate = Name::new(&self.spelling);
                // The candidate's own suffix is at least the group's next,
                // so only a base spelled like it can have taken it.
                let other = self
                    .bases
                    .get(&candidate)
                    .copied()
                    .filter(|other| self.base_taken(*other, depth));
                if let Some(other) = other {
                    self.skip(group, next, other);
                } else if self.raw.contains(&candidate) {
                    self.skip(group, next, NONE);
                } else {
                    break candidate;
                }
            }
            next += 1;
        };
        let row = &mut self.groups[index];
        row.next = next + 1;
        if zero {
            row.zero = Some(name);
        }
        name
    }

    /// Record that `(group, suffix)` was passed over, pointing the marks
    /// of `target` (the group itself for suffix zero, else the group spelled
    /// like the candidate, or `NONE`) at the entry.
    fn skip(&mut self, group: u32, suffix: u32, target: u32) {
        let entry = self.skipped.len() as u32;
        self.skipped.push([group, suffix]);
        let previous = if target == NONE {
            NONE
        } else {
            let marks = &mut self.marks[target as usize];
            let pointer = if suffix == 0 {
                &mut marks.zero_skip
            } else {
                &mut marks.as_skip
            };
            std::mem::replace(pointer, entry)
        };
        self.skip_undo.push([target, previous]);
    }
}

/// The part of `name` before a final `$` and the number after it, when that
/// is a positive decimal without leading zeros that fits a suffix.
fn canonical_suffix(name: &str) -> Option<(&str, u32)> {
    let (prefix, suffix) = name.rsplit_once('$')?;
    if suffix.starts_with(|c: char| ('1'..='9').contains(&c))
        && suffix.bytes().all(|c| c.is_ascii_digit())
    {
        suffix.parse().ok().map(|suffix| (prefix, suffix))
    } else {
        None
    }
}

/// Append `value` in decimal, without allocating.
fn push_decimal(out: &mut String, value: u32) {
    let mut digits = [0u8; 10];
    let mut start = digits.len();
    let mut rest = value;
    loop {
        start -= 1;
        digits[start] = b'0' + (rest % 10) as u8;
        rest /= 10;
        if rest == 0 {
            break;
        }
    }
    for digit in &digits[start..] {
        out.push(char::from(*digit));
    }
}

/// The names of one unit, by what they name. Reused between units.
#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct Printed {
    /// Dense by variable (a copy has an entry of its own).
    pub(crate) names: Vec<Option<Name>>,
    /// Dense by import.
    pub(crate) modules: Vec<Option<Name>>,
    /// The cached bounds of range loops, in print order.
    pub(crate) finishes: Vec<Name>,
}

/// The free lists of a unit's functions as identifiers, back to back;
/// `ends[i]` is where list `i` ends.
#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct FreeLists {
    pub(crate) idents: Vec<Ident>,
    pub(crate) ends: Vec<u32>,
}

/// The names of the replay against the names of the pass.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize)]
pub(crate) struct NameStats {
    /// Identifiers the pass names, other than stamp-zero identifiers
    /// (printed as they are spelled).
    pub(crate) names_pass: usize,
    /// Variables and modules the replay names.
    pub(crate) names_replayed: usize,
    /// Variables and modules whose name is not the pass's name of their
    /// identifier, plus identifiers the pass names and the replay does not.
    pub(crate) name_differences: usize,
    /// Cached bounds whose spelling one side has and the other has not
    /// (as multisets).
    pub(crate) finish_differences: usize,
    /// Free lists one side has and the other has not (as multisets of
    /// identifier sequences). A difference here with no name difference is
    /// a latent one: no local of the unit has the base that differs.
    pub(crate) free_differences: usize,
}

/// Check mode: the replay's names against `Names::collect` on `program`,
/// the lowering's own program before the JS passes with its module list
/// filled in. `idents[var]` is the identifier of a variable (read through
/// its origin by the caller: one entry per variable) and `modules[import]`
/// that of an import. `Err` when the pass does not support the unit (no
/// comparison). Check mode only. One hash lookup per named variable and
/// module and one per entry of the pass's tables (the pass is keyed by
/// identifier); two sorts for the cached bounds and two for the free lists.
pub(crate) fn compare_with_pass(
    printed: &Printed,
    idents: &[Ident],
    modules: &[Ident],
    free: &FreeLists,
    program: &JsDepsProgram,
    resolver: &ModulePathResolver,
    jsx_preserve: bool,
) -> Result<NameStats, Unsupported> {
    let names = Names::collect(program, resolver, jsx_preserve)?;
    let mut stats = NameStats::default();
    // The identifiers the replay names, once each (copies print as their
    // origin's identifier).
    let mut replayed: HashSet<Ident> = HashSet::with_capacity(printed.names.len());
    // A module is named under the suffix rule whatever its stamp; another
    // identifier of stamp zero prints as it is spelled.
    let module_set: HashSet<Ident> = modules.iter().copied().collect();
    let named = printed
        .names
        .iter()
        .zip(idents)
        .map(|(name, ident)| (name, ident, false))
        .chain(printed.modules.iter().zip(modules).map(|(name, ident)| (name, ident, true)));
    for (name, ident, module) in named {
        let Some(name) = name else { continue };
        if ident.stamp() == 0 && !module {
            continue;
        }
        if !replayed.insert(*ident) {
            continue;
        }
        if names.printed.get(ident) != Some(name) {
            stats.name_differences += 1;
        }
    }
    stats.names_replayed = replayed.len();
    for ident in names.printed.keys() {
        if ident.stamp() == 0 && !module_set.contains(ident) {
            continue;
        }
        stats.names_pass += 1;
        if !replayed.contains(ident) {
            stats.name_differences += 1;
        }
    }
    let mut pass_finishes: Vec<&str> = names.finishes.values().map(|name| name.as_str()).collect();
    let mut replay_finishes: Vec<&str> = printed.finishes.iter().map(|name| name.as_str()).collect();
    stats.finish_differences = multiset_difference(&mut pass_finishes, &mut replay_finishes);
    // Free lists as sets of identifier sequences: a function the lowering
    // copied is one sequence for both sides.
    let mut pass_free: Vec<&[Ident]> = names.free.values().map(Vec::as_slice).collect();
    let mut replay_free: Vec<&[Ident]> = Vec::with_capacity(free.ends.len());
    let mut start = 0;
    for &end in &free.ends {
        replay_free.push(&free.idents[start..end as usize]);
        start = end as usize;
    }
    pass_free.sort_unstable();
    pass_free.dedup();
    replay_free.sort_unstable();
    replay_free.dedup();
    stats.free_differences = multiset_difference(&mut pass_free, &mut replay_free);
    Ok(stats)
}

/// The pass's free lists and names of `program`, sorted, for the text a
/// failing oracle test shows beside the replay's (`bir::lower::oracle_tests`).
#[cfg(test)]
pub(crate) fn pass_tables(
    program: &JsDepsProgram,
    resolver: &ModulePathResolver,
    jsx_preserve: bool,
) -> Result<(Vec<Vec<Ident>>, Vec<(Ident, Name)>), Unsupported> {
    let names = Names::collect(program, resolver, jsx_preserve)?;
    let mut free: Vec<Vec<Ident>> = names.free.values().cloned().collect();
    free.sort_unstable();
    let mut printed: Vec<(Ident, Name)> = names.printed.iter().map(|(ident, name)| (*ident, *name)).collect();
    printed.sort_unstable_by_key(|(ident, _)| *ident);
    Ok((free, printed))
}

/// The entries one sorted side has and the other has not, as multisets.
/// Sorts both. One step per entry after the sorts.
fn multiset_difference<T: Ord>(left: &mut [T], right: &mut [T]) -> usize {
    left.sort_unstable();
    right.sort_unstable();
    let (mut i, mut j, mut differences) = (0, 0, 0);
    while i < left.len() && j < right.len() {
        match left[i].cmp(&right[j]) {
            std::cmp::Ordering::Less => {
                differences += 1;
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                differences += 1;
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                i += 1;
                j += 1;
            }
        }
    }
    differences + (left.len() - i) + (right.len() - j)
}

// Child order is the legacy printer's order. Shape decisions remain in walk;
// constructs not yet handled by Build keep exactly their existing fallback.
fn children(
    a: &JsArena,
    e: Expr,
    jsx_preserve: bool,
    mut visit: impl FnMut(Expr) -> Result<(), Unsupported>,
) -> Result<(), Unsupported> {
    match a.ek(e) {
        ExprKind::Var(_) | ExprKind::Qualified(_) | ExprKind::Fun(_) => {
            unreachable!("handled by caller")
        }
        ExprKind::Number(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Null
        | ExprKind::Undefined { .. } => {}
        ExprKind::Length(e, _)
        | ExprKind::IsNullOrUndefined(e)
        | ExprKind::Typeof(e)
        | ExprKind::JsNot(e)
        | ExprKind::JsBnot(e)
        | ExprKind::OptionalBlock(e, true)
        | ExprKind::CamlBlockTag(e, _)
        | ExprKind::Await(e)
        | ExprKind::Spread(e) => visit(e)?,
        ExprKind::StaticIndex(e, _, _) => visit(e)?,
        ExprKind::Bin(crate::js_ir::op::BinOp::Eq, l, r) => {
            walk::assignment_target(a, l)?;
            visit(l)?;
            visit(r)?;
        }
        ExprKind::Bin(op, l, r) => {
            if let Some(target) = walk::nullish_target(a, op, l, r)? {
                visit(target)?;
            } else {
                visit(l)?;
                visit(r)?;
            }
        }
        ExprKind::In(l, r) | ExprKind::Seq(l, r) | ExprKind::ArrayIndex(l, r) => {
            visit(l)?;
            visit(r)?;
        }
        ExprKind::Cond(c, t, f) => {
            visit(c)?;
            visit(t)?;
            visit(f)?;
        }
        ExprKind::Call(f, args, _) => {
            walk::call_supported(a, f)?;
            visit(f)?;
            for e in a.exprs(args) {
                visit(*e)?;
            }
        }
        ExprKind::New(f, args) => {
            visit(f)?;
            if let Some(args) = args {
                for e in a.exprs(args) {
                    visit(*e)?;
                }
            }
        }
        ExprKind::Array(items, _) => {
            for e in a.exprs(items) {
                visit(*e)?;
            }
        }
        ExprKind::Object(props) => {
            for (_, e) in a.props(props) {
                visit(*e)?;
            }
        }
        ExprKind::CamlBlock(items, _, tag) => {
            let (items, tag) = (a.exprs(items), a.tag(tag));
            walk::block_supported(items, tag)?;
            for (_, e) in walk::block_elements(a, items, tag) {
                visit(e)?;
            }
        }
        ExprKind::RawJsCode(_) => {}
        ExprKind::Jsx(id) => {
            let (jsx, form) = walk::jsx_form(a, id, jsx_preserve)?;
            if matches!(form, walk::JsxForm::Runtime) {
                visit(jsx.callee)?;
            }
            if !matches!(form, walk::JsxForm::Fragment) {
                visit(jsx.tag)?;
            }
            if !matches!(form, walk::JsxForm::Runtime)
                && let Some(key) = jsx.key
            {
                visit(key)?;
            }
            if let Some(spread) = jsx.spread {
                visit(spread)?;
            }
            for (_, value) in a.props(jsx.props) {
                visit(*value)?;
            }
            if let Some(children) = jsx.children {
                for child in a.exprs(children) {
                    visit(*child)?;
                }
            }
            if matches!(form, walk::JsxForm::Runtime)
                && let Some(key) = jsx.key
            {
                visit(key)?;
            }
        }
        ExprKind::TemplateLiteral(_) | ExprKind::JsonLiteral(_) => {}
        ExprKind::InterpolatedTemplate(segments, values) => {
            walk::template_supported(a.segments(segments).len(), a.exprs(values).len())?;
            for e in a.exprs(values) {
                visit(*e)?;
            }
        }
        ExprKind::TaggedTemplate(tag, strings, values) => {
            walk::template_supported(a.tagged(strings).len(), a.exprs(values).len())?;
            visit(tag)?;
            for e in a.exprs(values) {
                visit(*e)?;
            }
        }
        // Legacy .apply meets the callee before the argument array.
        ExprKind::FlatCall(func, args) => {
            visit(func)?;
            visit(args)?;
        }
        ExprKind::OptionalBlock(inner, false) => {
            if let Some(inner) = walk::optional_argument(a, inner) {
                visit(inner)?;
            }
        }
        ExprKind::RecordRest(_, source) => visit(source)?,
        ExprKind::StringAppend(..) => unreachable!("iterative string traversal in caller"),
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::js_ir::arena::{FunInfo, JsProgram};

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }
    fn names() -> Names {
        Names {
            scopes: vec![Scope::default()],
            budget: 1_000_000,
            ..Names::default()
        }
    }

    #[test]
    fn collect_rejects_comments_before_assigning_names() {
        use crate::js_ir::arena::JsProgram;
        let mut a = JsArena::new();
        let e = a.expr_commented(ExprKind::Null, "keep this comment");
        let s = a.stmt(StmtKind::Exp(e));
        let p = JsDepsProgram {
            program: JsProgram::new_in(vec![s], vec![], a),
            modules: vec![],
            side_effect: None,
        };
        let resolver =
            ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
        assert_eq!(
            Names::collect(&p, &resolver, false).err(),
            Some(Unsupported("non-decoration expression comment"))
        );
    }

    #[test]
    fn block_shape_rejections_match_builder() {
        use crate::js_ir::op::MutableFlag;
        use crate::lambda::TagInfo;
        let TagInfo::Constructor(mut constructor) = TagInfo::constructor("A", 1) else {
            unreachable!()
        };
        constructor.runtime.tag.literal = crate::types::VariantLiteralTag::Float("0x1p0".into());
        for (tag, reason) in [
            (
                TagInfo::poly_var("empty"),
                "block literal: empty polymorphic variant",
            ),
            (
                TagInfo::Constructor(constructor),
                "block literal: float tag",
            ),
        ] {
            let mut a = JsArena::new();
            let items = a.expr_list(&[]);
            let tag = a.tag_id(tag);
            let e = a.expr(ExprKind::CamlBlock(items, MutableFlag::Immutable, tag));
            let mut n = names();
            assert_eq!(
                n.analyze_expr(&a, e, &mut HashSet::new(), &mut HashSet::new()),
                Err(Unsupported(reason))
            );
            assert_eq!(n.expr(&a, e), Err(Unsupported(reason)));
            let allocator = oxc_allocator::Allocator::default();
            let builder = super::super::build::Build::new(&allocator, &a, &n);
            assert_eq!(builder.expr(e).err(), Some(Unsupported(reason)));
        }
    }
    #[test]
    fn suffixes_respect_other_bases_and_raw_globals() {
        let mut n = names();
        n.raw.insert(Name::new("x$2"));
        n.add(id("x$1", 1), false).unwrap();
        n.add(id("x", 2), false).unwrap();
        n.add(id("x", 3), false).unwrap();
        assert_eq!(n.get(&id("x", 3)), "x$3");
        n.add(id("default", 4), false).unwrap();
        assert_eq!(n.get(&id("default", 4)), "$$default");
    }

    #[test]
    fn captures_inherit_whole_groups_but_siblings_do_not_leak() {
        let mut n = names();
        let (a, b, c, d) = (id("x", 1), id("x", 2), id("x", 3), id("x", 4));
        n.add(a, false).unwrap();
        n.add(b, false).unwrap();
        n.enter(&[a]).unwrap();
        n.add(c, false).unwrap();
        assert_eq!(n.get(&c), "x$2");
        n.leave();
        n.enter(&[]).unwrap();
        n.add(d, false).unwrap();
        assert_eq!(n.get(&d), "x");
        // Lookup of a still-visible outer id is independent of the empty table.
        n.add(a, false).unwrap();
        n.enter(&[a]).unwrap();
        let e = id("x", 5);
        n.add(e, false).unwrap();
        assert_eq!(n.get(&e), "x$1");
        n.leave();
        n.leave();
        assert_eq!(n.visible[&b], Name::new("x$1"));
    }

    #[test]
    fn entry_shares_large_suffix_tables() {
        let mut n = names();
        for stamp in 1..=2_000 {
            n.add(id("x", stamp), false).unwrap();
        }
        n.enter(&[id("x", 1)]).unwrap();
        let base = Name::new("x");
        let outer = &n.scopes[0].groups[&base];
        let inner = &n.scopes[1].groups[&base];
        assert!(outer.stamps.ptr_eq(&inner.stamps));
        assert!(outer.used.ptr_eq(&inner.used));
        n.leave();
    }

    #[test]
    fn work_budget_fails_closed() {
        let mut n = names();
        n.budget = 10;
        for i in 1..20 {
            n.raw.insert(Name::new(&format!("x${i}")));
        }
        n.add(id("x", 1), false).unwrap();
        assert_eq!(
            n.add(id("x", 2), false),
            Err(Unsupported("scoped naming work budget"))
        );
        assert_eq!(n.steps, 11);
    }

    #[test]
    fn deep_functions_have_linear_naming_work() {
        std::thread::Builder::new()
            .stack_size(32 * 1024 * 1024)
            .spawn(|| {
                fn measure(depth: i32) -> usize {
                    let mut a = JsArena::new();
                    let mut expr = a.expr(ExprKind::Null);
                    for stamp in (1..=depth).rev() {
                        let own = id("x", stamp);
                        let own_id = a.ident_id(own);
                        let own_expr = a.expr(ExprKind::Var(own_id));
                        let parent_id = a.ident_id(id("x", stamp - 1));
                        let parent_expr = a.expr(ExprKind::Var(parent_id));
                        let items = a.expr_list(&[own_expr, parent_expr, expr]);
                        let array = a.expr(ExprKind::Array(
                            items,
                            crate::js_ir::op::MutableFlag::Immutable,
                        ));
                        let ret = a.stmt(StmtKind::Return(array));
                        let body = a.stmt_list(&[ret]);
                        let params = a.ident_list(&[own]);
                        let f = a.fun_id(FunInfo {
                            is_method: false,
                            params,
                            body,
                            return_unit: false,
                            async_: false,
                            directive: None,
                        });
                        expr = a.expr(ExprKind::Fun(f));
                    }
                    let s = a.stmt(StmtKind::Exp(expr));
                    let p = JsDepsProgram {
                        program: JsProgram::new_in(vec![s], vec![], a),
                        modules: vec![],
                        side_effect: None,
                    };
                    let resolver = ModulePathResolver::from_compile_options(
                        None, None, None, None, None, None, false,
                    );
                    let names = Names::collect(&p, &resolver, false).unwrap();
                    assert_eq!(names.get(&id("x", depth)), format!("x${depth}"));
                    assert!(names.steps < depth as usize * 40, "{}", names.steps);
                    names.steps
                }
                let small = measure(1_000);
                let large = measure(2_000);
                assert!(large <= small * 2 + 16, "{small} -> {large}");
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[cfg(test)]
mod replay_tests {
    use super::*;

    #[test]
    fn replay_sizes() {
        assert_eq!(std::mem::size_of::<Subject>(), 16);
        assert_eq!(std::mem::size_of::<GroupRow>(), 16);
        assert_eq!(std::mem::size_of::<Saved>(), 24);
        assert_eq!(std::mem::size_of::<Level>(), 12);
        assert_eq!(std::mem::size_of::<NameStats>(), 40);
    }

    #[test]
    fn group_marks_size() {
        assert_eq!(std::mem::size_of::<Marks>(), 32);
    }

    #[test]
    fn default_tables_are_empty() {
        let t = Tables::default();
        assert!(t.groups.is_empty() && t.bases.is_empty() && t.slot_group.is_empty() && t.visible.is_empty());
        assert!(t.saved.is_empty() && t.assigned.is_empty() && t.skipped.is_empty() && t.levels.is_empty());
        assert!(t.raw.is_empty() && t.spelling.is_empty());
        assert_eq!((t.synthetic, t.steps), (0, 0));
        let row = GroupRow { next: 0, scope: 0, zero: None };
        let saved = Saved { group: 0, row };
        assert_eq!((saved.group, saved.row.next, saved.row.scope, saved.row.zero), (0, 0, 0, None));
        let level = Level { saved: 0, assigned: 0, skipped: 0 };
        assert_eq!(level.saved + level.assigned + level.skipped, 0);
    }

    #[test]
    fn a_module_with_stamp_zero_is_named_like_any_other() {
        let mut t = tables(2, &[]);
        assert_eq!(t.add_module(subject("Foo", 0, 0)).as_str(), "Foo");
        assert_eq!(t.add(subject("Foo", 5, 1)).as_str(), "Foo$1");
    }

    fn subject(name: &str, stamp: i32, slot: u32) -> Subject {
        Subject { slot, stamp, name: Name::new(name) }
    }
    fn tables(slots: usize, raw: &[&str]) -> Tables {
        let raw: Vec<Name> = raw.iter().map(|name| Name::new(name)).collect();
        let mut tables = Tables::default();
        tables.begin(slots, &raw);
        tables
    }

    #[test]
    fn the_tables_skip_other_bases_and_raw_names() {
        // `suffixes_respect_other_bases_and_raw_globals`, on the tables.
        let mut t = tables(4, &["x$2"]);
        assert_eq!(t.add(subject("x$1", 1, 0)).as_str(), "x$1");
        assert_eq!(t.add(subject("x", 2, 1)).as_str(), "x");
        // `x$1` is another base's name, `x$2` a raw name.
        assert_eq!(t.add(subject("x", 3, 2)).as_str(), "x$3");
        assert_eq!(t.add(subject("default", 4, 3)).as_str(), "$$default");
        // A visible identifier keeps its name.
        assert_eq!(t.add(subject("x", 3, 2)).as_str(), "x$3");
    }

    #[test]
    fn the_tables_inherit_whole_groups_and_siblings_do_not_leak() {
        // `captures_inherit_whole_groups_but_siblings_do_not_leak`, on the
        // tables.
        let mut t = tables(5, &[]);
        let (a, b, c, d, e) = (subject("x", 1, 0), subject("x", 2, 1), subject("x", 3, 2), subject("x", 4, 3), subject("x", 5, 4));
        assert_eq!((t.add(a).as_str(), t.add(b).as_str()), ("x", "x$1"));
        assert!(!t.reserve(a));
        t.enter(&[a]);
        assert_eq!(t.add(c).as_str(), "x$2");
        t.leave();
        t.enter(&[]);
        assert_eq!(t.add(d).as_str(), "x");
        // The outer identifier is visible whatever the scope inherited.
        assert_eq!(t.add(a).as_str(), "x");
        t.enter(&[a]);
        assert_eq!(t.add(e).as_str(), "x$1");
        t.leave();
        t.leave();
        assert_eq!(t.add(b).as_str(), "x$1");
        // The name `c` had in the first function is free again there, not
        // in the program: the program's next `x` is `x$2`.
        assert_eq!(t.add(c).as_str(), "x$2");
    }

    #[test]
    fn a_reservation_reports_a_first_name_and_stamp_zero_reserves_its_base() {
        let mut t = tables(3, &[]);
        assert!(t.reserve(subject("x", 1, 0)));
        assert!(!t.reserve(subject("x", 1, 0)));
        // Stamp zero prints as it is spelled and takes the base.
        assert!(!t.reserve(subject("y", 0, 1)));
        assert_eq!(t.add(subject("y", 0, 1)).as_str(), "y");
        assert_eq!(t.add(subject("y", 7, 2)).as_str(), "y$1");
    }

    #[test]
    fn a_synthetic_name_takes_a_suffix_in_its_scope() {
        // `the_cached_bound_of_a_range_loop_takes_a_name_in_its_scope`.
        let mut t = tables(2, &[]);
        assert_eq!(t.add(subject("i", 1, 0)).as_str(), "i");
        assert_eq!(t.synthetic(Name::new("i_finish")).as_str(), "i_finish");
        assert_eq!(t.synthetic(Name::new("i_finish")).as_str(), "i_finish$1");
        assert_eq!(t.add(subject("i_finish", 2, 1)).as_str(), "i_finish$2");
    }

    /// The steps of naming `count` variables of one base, then `count`
    /// times entering a function that inherits the base and names one more.
    fn steps_of(count: u32) -> usize {
        let mut t = tables(2 * count as usize, &[]);
        let first = subject("x", 1, 0);
        for index in 0..count {
            t.add(subject("x", index as i32 + 1, index));
        }
        for index in count..2 * count {
            t.enter(&[first]);
            t.add(subject("x", index as i32 + 1, index));
            t.leave();
        }
        t.steps
    }

    #[test]
    fn ten_thousand_names_and_scopes_cost_a_constant_number_of_steps_each() {
        // Entering a function that inherits a group of 10,000 names costs
        // what entering one that inherits a group of 5,000 costs.
        let (small, large) = (steps_of(5_000), steps_of(10_000));
        assert_eq!(large, 2 * small);
        assert!(large <= 10_000 * 8, "{large}");
    }

    #[test]
    fn warm_tables_allocate_nothing() {
        let run = |t: &mut Tables| {
            t.begin(20_000, &[]);
            let first = subject("x", 1, 0);
            for index in 0..10_000u32 {
                t.add(subject("x", index as i32 + 1, index));
            }
            for index in 10_000..20_000u32 {
                t.enter(&[first]);
                t.add(subject("x", index as i32 + 1, index));
                t.leave();
            }
        };
        let mut t = Tables::default();
        run(&mut t);
        let allocations = allocation_counter::measure(|| run(&mut t));
        assert_eq!(allocations.count_total, 0, "{allocations:?}");
    }

    #[test]
    fn the_comparison_counts_what_the_replay_gets_wrong() {
        // `let x = 1`, exported: the pass names it `x`, has no cached bound
        // and no function.
        let mut a = JsArena::new();
        let x = Ident::new("x", 1, crate::ident::IdentFlags::NONE);
        let one = crate::js_ir::build::exp::int(1, &mut a);
        let declaration = crate::js_ir::build::stmt::define(x, Some(one), crate::lambda::lam_compat::LetKind::Strict, &mut a);
        let program = JsDepsProgram {
            program: crate::js_ir::arena::JsProgram::new_in(vec![declaration], vec![x], a),
            modules: vec![],
            side_effect: None,
        };
        let resolver = ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
        let compare = |name: Option<&str>, finishes: &[&str], free: FreeLists| {
            let printed = Printed {
                names: vec![name.map(Name::new)],
                modules: vec![],
                finishes: finishes.iter().map(|name| Name::new(name)).collect(),
            };
            compare_with_pass(&printed, &[x], &[], &free, &program, &resolver, false).unwrap()
        };
        let equal = compare(Some("x"), &[], FreeLists::default());
        assert_eq!(equal, NameStats { names_pass: 1, names_replayed: 1, ..NameStats::default() });
        assert_eq!(compare(Some("x$1"), &[], FreeLists::default()).name_differences, 1);
        // Named by the pass only.
        assert_eq!(compare(None, &[], FreeLists::default()).name_differences, 1);
        assert_eq!(compare(Some("x"), &["i_finish"], FreeLists::default()).finish_differences, 1);
        let extra = FreeLists { idents: vec![x], ends: vec![1] };
        assert_eq!(compare(Some("x"), &[], extra).free_differences, 1);
    }
}

/// The names the pass gives on the programs the naming log of the backend
/// lowering has to get right (THREE_TREES 11.4, "T5 part B as redesigned").
/// They pin the expected names; the log's own tests assert the same ones.
#[cfg(test)]
mod counterexample_tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::js_ir::arena::{ForRangeInfo, FunInfo, JsProgram};
    use crate::js_ir::op::MutableFlag;
    use crate::lambda::lam_compat::LetKind;

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }
    fn var(a: &mut JsArena, id: Ident) -> Expr {
        crate::js_ir::build::exp::var(id, a)
    }
    /// `[items]`: an expression that reads its operands and is no call (a
    /// function whose body returns a call of a variable is eta-reduced).
    fn read(a: &mut JsArena, items: &[Ident]) -> Expr {
        let items: Vec<Expr> = items.iter().map(|id| var(a, *id)).collect();
        crate::js_ir::build::exp::array(&items, MutableFlag::Immutable, a)
    }
    fn fun(a: &mut JsArena, params: &[Ident], body: &[Stmt], is_method: bool) -> Expr {
        let (params, body) = (a.ident_list(params), a.stmt_list(body));
        let f = a.fun_id(FunInfo { is_method, params, body, return_unit: false, async_: false, directive: None });
        a.expr(ExprKind::Fun(f))
    }
    fn define(a: &mut JsArena, id: Ident, value: Expr) -> Stmt {
        crate::js_ir::build::stmt::define(id, Some(value), LetKind::Strict, a)
    }
    fn ret(a: &mut JsArena, value: Expr) -> Stmt {
        a.stmt(StmtKind::Return(value))
    }
    fn collect(a: JsArena, block: Vec<Stmt>, exports: Vec<Ident>) -> Names {
        let p = JsDepsProgram { program: JsProgram::new_in(block, exports, a), modules: vec![], side_effect: None };
        let resolver = ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
        Names::collect(&p, &resolver, false).unwrap()
    }

    /// `let f = p => { let v = [p]; let g = () => { let v' = [captured]; return [v'] }; return [g] }`.
    fn nested(capture_outer_local: bool) -> (Names, Ident, Ident) {
        let (f, p, v, g, inner) = (id("f", 1), id("p", 2), id("v", 3), id("g", 4), id("v", 5));
        let mut a = JsArena::new();
        let captured = read(&mut a, &[if capture_outer_local { v } else { p }]);
        let declare_inner = define(&mut a, inner, captured);
        let result = read(&mut a, &[inner]);
        let result = ret(&mut a, result);
        let g_value = fun(&mut a, &[], &[declare_inner, result], false);
        let value = read(&mut a, &[p]);
        let declare_v = define(&mut a, v, value);
        let declare_g = define(&mut a, g, g_value);
        let result = read(&mut a, &[g]);
        let result = ret(&mut a, result);
        let f_value = fun(&mut a, &[p], &[declare_v, declare_g, result], false);
        let declare_f = define(&mut a, f, f_value);
        (collect(a, vec![declare_f], vec![f]), v, inner)
    }

    #[test]
    fn a_function_nested_in_a_function_inherits_the_names_of_the_outer_local_it_captures() {
        // Gap 1 (a): `v` is free in `g`, so `g`'s scope inherits the names
        // of base `v` and its own `v` is `v$1`.
        let (names, v, inner) = nested(true);
        assert_eq!((names.get(&v), names.get(&inner)), ("v", "v$1"));
        // Without the capture `g` inherits nothing of base `v`.
        let (names, v, inner) = nested(false);
        assert_eq!((names.get(&v), names.get(&inner)), ("v", "v"));
    }

    #[test]
    fn a_function_inherits_the_names_of_what_an_expression_moved_into_it_reads() {
        // G10: `let f = param => { return param' => g(param, param') }`,
        // the eta-expansion of a partial application whose argument reads
        // the local `param`: the fresh parameter is `param$1`.
        let (f, param, fresh, g) = (id("f", 1), id("param", 2), id("param", 3), id("g", 10));
        let mut a = JsArena::new();
        let callee = var(&mut a, g);
        let args = [var(&mut a, param), var(&mut a, fresh)];
        let call = crate::js_ir::build::exp::call(callee, &args, Default::default(), &mut a);
        let result = ret(&mut a, call);
        let expansion = fun(&mut a, &[fresh], &[result], false);
        let result = ret(&mut a, expansion);
        let f_value = fun(&mut a, &[param], &[result], false);
        let declare_f = define(&mut a, f, f_value);
        let names = collect(a, vec![declare_f], vec![f]);
        assert_eq!((names.get(&param), names.get(&fresh)), ("param", "param$1"));
    }

    #[test]
    fn a_recursive_inner_function_is_not_free_in_the_function_that_declares_it() {
        // Gap 1 (b): `let f = () => { let g = () => [g]; return [g] }; let g' = 1`.
        // `g` is free in itself and bound in `f`: `f` reserves nothing in
        // the program, so the program's own `g'` is `g`, not `g$1`.
        let (f, g, top) = (id("f", 1), id("g", 2), id("g", 3));
        let mut a = JsArena::new();
        let itself = read(&mut a, &[g]);
        let itself = ret(&mut a, itself);
        let g_value = fun(&mut a, &[], &[itself], false);
        let declare_g = define(&mut a, g, g_value);
        let result = read(&mut a, &[g]);
        let result = ret(&mut a, result);
        let f_value = fun(&mut a, &[], &[declare_g, result], false);
        let declare_f = define(&mut a, f, f_value);
        let one = crate::js_ir::build::exp::int(1, &mut a);
        let declare_top = define(&mut a, top, one);
        let names = collect(a, vec![declare_f, declare_top], vec![f, top]);
        assert_eq!((names.get(&g), names.get(&top)), ("g", "g"));
    }

    #[test]
    fn the_this_of_a_method_is_named_only_when_the_body_reads_it() {
        // Gap 3: `let m = function (o, x) { return [read] }` as a method.
        for used in [false, true] {
            let (m, this, x) = (id("m", 1), id("o", 2), id("x", 3));
            let mut a = JsArena::new();
            let result = read(&mut a, &[if used { this } else { x }]);
            let result = ret(&mut a, result);
            let value = fun(&mut a, &[this, x], &[result], true);
            let declare = define(&mut a, m, value);
            let names = collect(a, vec![declare], vec![m]);
            assert_eq!(names.printed.get(&this).map(|name| name.as_str()), used.then_some("o"));
            assert_eq!(names.get(&x), "x");
        }
    }

    #[test]
    fn a_suffix_skips_a_raw_javascript_name_of_the_program() {
        // Gap 3: `[x$1']; let x = 1; let x' = 2` where `x$1'` is a
        // JavaScript name: the second `x` is `x$2`.
        let raw = Ident::new("x$1", 0, IdentFlags::JS);
        let (first, second) = (id("x", 1), id("x", 2));
        let mut a = JsArena::new();
        let value = read(&mut a, &[raw]);
        let effect = a.stmt(StmtKind::Exp(value));
        let one = crate::js_ir::build::exp::int(1, &mut a);
        let declare_first = define(&mut a, first, one);
        let two = crate::js_ir::build::exp::int(2, &mut a);
        let declare_second = define(&mut a, second, two);
        let names = collect(a, vec![effect, declare_first, declare_second], vec![first, second]);
        assert_eq!((names.get(&first), names.get(&second)), ("x", "x$2"));
    }

    #[test]
    fn the_cached_bound_of_a_range_loop_takes_a_name_in_its_scope() {
        // `for (let i = 1, i_finish = [n]; ...) {}; let i_finish' = 1`: the
        // bound is cached under `i_finish`, so the declaration after the
        // loop is `i_finish$1`. A statement names more than its binders.
        let (n, i, later) = (id("n", 1), id("i", 2), id("i_finish", 3));
        let mut a = JsArena::new();
        let one = crate::js_ir::build::exp::int(1, &mut a);
        let declare_n = define(&mut a, n, one);
        let init = crate::js_ir::build::exp::int(1, &mut a);
        let end = read(&mut a, &[n]);
        let (ident, body) = (a.ident_id(i), a.stmt_list(&[]));
        let range = a.for_range_id(ForRangeInfo {
            label: None,
            init: Some(init),
            end,
            ident,
            direction: crate::js_ir::ForDirection::Upto,
            body,
        });
        let loop_ = a.stmt(StmtKind::ForRange(range));
        let one = crate::js_ir::build::exp::int(1, &mut a);
        let declare_later = define(&mut a, later, one);
        let names = collect(a, vec![declare_n, loop_, declare_later], vec![n, later]);
        assert_eq!((names.get(&i), names.finish(loop_), names.get(&later)), ("i", "i_finish", "i_finish$1"));
    }

    #[test]
    fn two_function_literals_of_one_statement_name_what_they_capture_in_print_order() {
        // `[() => [x], () => [y]]; let a = 1; let a' = 2`, where the
        // literals capture the two `a`s declared after them: the literal
        // printed first names its variable `a`, whatever the stamps. The
        // order of two literals inside one statement is a naming fact.
        for swapped in [false, true] {
            let (first, second) = (id("a", 1), id("a", 2));
            let mut a = JsArena::new();
            let (left, right) = if swapped { (first, second) } else { (second, first) };
            let body = read(&mut a, &[left]);
            let body = ret(&mut a, body);
            let left_fun = fun(&mut a, &[], &[body], false);
            let body = read(&mut a, &[right]);
            let body = ret(&mut a, body);
            let right_fun = fun(&mut a, &[], &[body], false);
            let both = crate::js_ir::build::exp::array(&[left_fun, right_fun], MutableFlag::Immutable, &mut a);
            let effect = a.stmt(StmtKind::Exp(both));
            let one = crate::js_ir::build::exp::int(1, &mut a);
            let declare_first = define(&mut a, first, one);
            let two = crate::js_ir::build::exp::int(2, &mut a);
            let declare_second = define(&mut a, second, two);
            let names = collect(a, vec![effect, declare_first, declare_second], vec![first, second]);
            assert_eq!((names.get(&left), names.get(&right)), ("a", "a$1"));
        }
    }
}
