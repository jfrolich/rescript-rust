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
    steps: usize,
    budget: usize,
}
impl Names {
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
    ) -> Result<Self, Unsupported> {
        #[derive(Default)]
        struct Input {
            count: usize,
            raw: HashSet<Name>,
        }
        impl Visitor for Input {
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
        let mut defined: HashSet<_> = a.ident_slice(info.params).iter().copied().collect();
        let mut used = HashSet::new();
        self.analyze_block(a, a.stmts(info.body), &mut defined, &mut used)?;
        self.charge(used.len() + defined.len())?;
        used.retain(|id| !defined.contains(id));
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
            _ => children(a, e, |e| self.analyze_expr(a, e, defined, used))?,
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
                for id in a.ident_slice(info.params) {
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
        walk::expression_comment(a, e)?;
        match a.ek(e) {
            ExprKind::Var(id) => self.add(a.ident(id), false),
            ExprKind::Qualified(q) => self.add(a.qual(q).0.id, true),
            ExprKind::Fun(f) => self.function(a, f, None, false),
            _ => children(a, e, |e| self.expr(a, e)),
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

// Child order is the legacy printer's order. Shape decisions remain in walk;
// constructs not yet handled by Build keep exactly their existing fallback.
fn children(
    a: &JsArena,
    e: Expr,
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
        | ExprKind::StaticIndex(e, _, _)
        | ExprKind::OptionalBlock(e, _)
        | ExprKind::CamlBlockTag(e, _)
        | ExprKind::Await(e)
        | ExprKind::Spread(e) => visit(e)?,
        ExprKind::Bin(crate::js_ir::op::BinOp::Eq, l, r) => {
            walk::assignment_target(a, l)?;
            visit(l)?;
            visit(r)?;
        }
        ExprKind::Bin(_, l, r)
        | ExprKind::In(l, r)
        | ExprKind::Seq(l, r)
        | ExprKind::ArrayIndex(l, r) => {
            visit(l)?;
            visit(r)?;
        }
        ExprKind::Cond(c, t, f) => {
            visit(c)?;
            visit(t)?;
            visit(f)?;
        }
        ExprKind::Call(f, args, _) => {
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
        ExprKind::RawJsCode(_) => return walk::raw_supported(),
        ExprKind::Jsx(_) => return Err(Unsupported("JSX")),
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
        ExprKind::FlatCall(..) => return Err(Unsupported("flat call")),
        ExprKind::RecordRest(..) => return Err(Unsupported("record rest")),
        ExprKind::StringAppend(..) => return Err(Unsupported("string concatenation association")),
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
                    let names = Names::collect(&p, &resolver).unwrap();
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
