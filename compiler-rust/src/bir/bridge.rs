//! Migration bridges. Source nodes are decoded once, with explicit postorder
//! stacks rather than recursive arena exports. The identity side tables preserve
//! legacy identifier flags/stamps without allocating from the legacy counter.
use super::*;
use crate::fast_hash::AHashMap;
use crate::ident::Ident;
use crate::lambda::arena::{Lam, LamArena, LamProgram, Node as L};
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_constant::Constant as C;
use crate::lambda::{DirectionFlag, SwitchDispatch};
use smallvec::{SmallVec, smallvec};

/// An ordinary migration fallback, never a compiler error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Unsupported(pub &'static str);
impl std::fmt::Display for Unsupported {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.0)
    }
}
impl std::error::Error for Unsupported {}

/// Imported tree and the legacy identities required by the temporary exporter.
/// This is bridge metadata, not a second copy of the source tree.
pub struct Imported {
    /// New arena.
    pub arena: Bir,
    /// The unit's root.
    pub root: NodeId,
    pub(super) idents: Vec<Ident>,
    pub(super) globals: Vec<Ident>,
    /// The legacy name of each static label a round created.
    labels: std::collections::BTreeMap<u32, u32>,
    #[cfg(test)]
    identifier_lookups: usize,
}

#[derive(Default)]
pub(super) struct Importer {
    pub(super) bir: Bir,
    vars: AHashMap<Ident, VarId>,
    idents: Vec<Ident>,
    globals: Vec<Ident>,
    #[cfg(test)]
    identifier_lookups: usize,
}
impl Importer {
    fn var(&mut self, ident: Ident) -> VarId {
        #[cfg(test)]
        {
            self.identifier_lookups += 1;
        }
        *self.vars.entry(ident).or_insert_with(|| {
            let v = self.bir.new_var_id(ident.name_atom(), ident.stamp() as u32);
            self.idents.push(ident);
            v
        })
    }
    fn span(&mut self, ids: &[Ident]) -> Result<VarSpan, Unsupported> {
        if ids.is_empty() {
            return Ok(VarSpan::default());
        }
        let first = self.var(ids[0]);
        for (offset, &ident) in ids.iter().enumerate().skip(1) {
            if self.var(ident).index() != first.index() + offset {
                return Err(Unsupported("non-contiguous binder run"));
            }
        }
        Ok(VarSpan {
            start: first.0,
            len: index(ids.len()),
        })
    }
    /// The imported program once `root` is complete.
    pub(super) fn finish(self, root: NodeId) -> Imported {
        Imported {
            arena: self.bir,
            root,
            idents: self.idents,
            globals: self.globals,
            labels: Default::default(),
            #[cfg(test)]
            identifier_lookups: self.identifier_lookups,
        }
    }
    pub(super) fn binders(&mut self, arena: &LamArena, node: L) -> Result<(), Unsupported> {
        match node {
            L::Function { info, .. } => {
                self.span(arena.params(info))?;
            }
            L::LetRec { ids, values, .. } => {
                self.span(arena.ident_run(ids, arena.list_len(values)))?;
            }
            L::StaticCatch { info, .. } => {
                let h = arena.catch_payload(info);
                if self.bir.pools.catch_labels.contains_key(&(h.label as u32)) {
                    return Err(Unsupported("reused static catch label"));
                }
                let params = self.span(arena.idents(h.params))?;
                self.bir.catch_header(h.label as u32, params);
            }
            L::Let { id, .. }
            | L::TryWith { id, .. }
            | L::For { id, .. }
            | L::ForOf { id, .. }
            | L::ForAwaitOf { id, .. } => {
                self.var(arena.ident(id));
            }
            _ => {}
        }
        Ok(())
    }
    fn constant(&mut self, value: &C) -> Result<ConstId, Unsupported> {
        enum Work<'a> {
            Enter(&'a C),
            Finish(&'a C, usize),
        }
        let mut work = vec![Work::Enter(value)];
        let mut values = Vec::new();
        while let Some(task) = work.pop() {
            let (c, count) = match task {
                Work::Enter(c) => {
                    let children: &[C] = match c {
                        C::Block { elements, .. } => elements,
                        C::Some(value) => std::slice::from_ref(value.as_ref()),
                        _ => &[],
                    };
                    work.push(Work::Finish(c, children.len()));
                    work.extend(children.iter().rev().map(Work::Enter));
                    continue;
                }
                Work::Finish(c, count) => (c, count),
            };
            let start = values.len() - count;
            let c = match c {
                C::JsNull => Constant::Null,
                C::JsUndefined { is_unit } => Constant::Undefined(*is_unit),
                C::JsTrue => Constant::Bool(true),
                C::JsFalse => Constant::Bool(false),
                C::Int { i, comment: None } => Constant::Int(i64::from(*i)),
                C::NativeInt { i, comment: None } => Constant::NativeInt(*i),
                C::Int {
                    i,
                    comment: Some(comment),
                } => Constant::DecoratedInt {
                    value: i64::from(*i),
                    native: false,
                    comment: *comment.clone(),
                },
                C::NativeInt {
                    i,
                    comment: Some(comment),
                } => Constant::DecoratedInt {
                    value: *i,
                    native: true,
                    comment: *comment.clone(),
                },
                C::Constructor(tag) => Constant::Constructor(tag.clone()),
                C::Char(c) => Constant::Char(*c as u32),
                C::String(s) => Constant::String(self.bir.intern_text(s)),
                C::ImmString(s) => Constant::ImmString(self.bir.intern_text(s)),
                C::Pointer(s) => Constant::Pointer(self.bir.intern_text(s)),
                C::Float(spelling) => {
                    let id = self.bir.intern_float(spelling)?;
                    values.truncate(start);
                    values.push(id);
                    continue;
                }
                C::BigInt { negative, value } => Constant::BigInt(self.bir.intern_text(&format!(
                    "{}{}",
                    if *negative { "-" } else { "+" },
                    value
                ))),
                C::Block { tag_info, .. } => Constant::Block {
                    tag: *tag_info.clone(),
                    fields: self.bir.const_fields(&values[start..]),
                },
                C::Some(_) => Constant::Some(values[start]),
                C::ModuleAlias => Constant::ModuleAlias,
            };
            values.truncate(start);
            values.push(self.bir.intern_const(c));
        }
        Ok(values[0])
    }
    pub(super) fn node(
        &mut self,
        a: &LamArena,
        node: L,
        c: &[NodeId],
    ) -> Result<NodeId, Unsupported> {
        let mut aux = 0;
        let view = match node {
            L::Var(id) => View::Var {
                var: self.var(a.ident(id)),
            },
            L::GlobalModule(id) => {
                let ident = a.ident(id);
                let path = self.bir.intern_text(ident.name());
                let module = self.bir.import(Import {
                    name: ident.name_atom(),
                    path,
                });
                if module.index() == self.globals.len() {
                    self.globals.push(ident);
                } else if self.globals[module.index()] != ident {
                    return Err(Unsupported("distinct global identities with one name"));
                }
                View::Global { module }
            }
            L::Const(id) => View::Const {
                value: self.constant(a.constant(id))?,
            },
            L::Apply { info, .. } => View::Apply {
                callee: c[0],
                args: &c[1..],
                info: self.bir.apply_info(a.apply_payload(info).info.clone()),
            },
            L::Function { info, .. } => {
                let h = a.func_payload(info);
                aux = u16::try_from(h.arity)
                    .map_err(|_| Unsupported("function arity outside u16"))?;
                let params = self.span(a.params(info))?;
                let header = self.bir.function_header(params, h.attr.clone(), h.loc);
                View::Fun { body: c[0], header }
            }
            L::Let { kind, id, .. } => {
                aux = kind as u16;
                View::Let {
                    var: self.var(a.ident(id)),
                    value: Some(c[0]),
                    body: c[1],
                }
            }
            L::LetRec { ids, values, .. } => {
                let span = self.span(a.ident_run(ids, a.list_len(values)))?;
                if span.is_empty() {
                    return Err(Unsupported("empty recursive binding group"));
                }
                View::LetRec {
                    first: VarId(span.start),
                    values: &c[..c.len() - 1],
                    body: c[c.len() - 1],
                }
            }
            L::Prim { info, .. } => {
                let p = a.prim_payload(info);
                let primitive = self.bir.intern_prim(PrimPayload {
                    primitive: p.primitive.clone(),
                    loc: p.loc,
                });
                View::Prim { args: c, primitive }
            }
            L::Switch { info, .. } => {
                let h = a.switch_payload(info);
                let keys = a
                    .switch_const_keys(info)
                    .iter()
                    .chain(a.switch_block_keys(info))
                    .cloned()
                    .map(CaseKey::Lambda)
                    .collect();
                let header = self.bir.switch_header(SwitchHeader {
                    keys,
                    clauses: vec![],
                    constants: index(h.n_consts()),
                    consts_full: h.consts_full,
                    blocks_full: h.blocks_full,
                    has_default: h.has_fail,
                    dispatch: h.dispatch.clone(),
                });
                View::Switch {
                    scrutinee: c[0],
                    actions: &c[1..],
                    header,
                }
            }
            L::StringSwitch { info, .. } => {
                let h = a.str_switch_payload(info);
                let keys = (0..h.n_cases())
                    .map(|i| CaseKey::String(self.bir.intern_text(a.str_switch_key(info, i))))
                    .collect();
                let header = self.bir.switch_header(SwitchHeader {
                    keys,
                    clauses: vec![],
                    constants: index(h.n_cases()),
                    consts_full: false,
                    blocks_full: false,
                    has_default: h.has_default,
                    dispatch: SwitchDispatch::Direct,
                });
                View::StrSwitch {
                    scrutinee: c[0],
                    actions: &c[1..],
                    header,
                }
            }
            L::StaticRaise { label, .. } => {
                if !self.bir.pools.catch_labels.contains_key(&(label as u32)) {
                    return Err(Unsupported("unbound static exit label"));
                }
                View::Exit {
                    label: label as u32,
                    args: c,
                }
            }
            L::StaticCatch { info, .. } => {
                let label = a.catch_payload(info).label as u32;
                let header = self.bir.pools.catch_labels[&label];
                View::Catch {
                    body: c[0],
                    handler: c[1],
                    header,
                }
            }
            L::TryWith { id, .. } => View::Try {
                body: c[0],
                exception: self.var(a.ident(id)),
                handler: c[1],
            },
            L::TryFinally { .. } => View::TryFinally {
                body: c[0],
                finaliser: c[1],
            },
            L::If { .. } => View::If {
                condition: c[0],
                then_: c[1],
                else_: c[2],
            },
            L::Sequence(..) => View::Seq {
                first: c[0],
                second: c[1],
            },
            L::Break => View::Break,
            L::Continue => View::Continue,
            L::While(..) => View::While {
                condition: c[0],
                body: c[1],
            },
            L::For { id, dir, .. } => {
                aux = dir as u16;
                View::For {
                    var: self.var(a.ident(id)),
                    parts: c,
                }
            }
            L::ForOf { id, .. } => View::ForOf {
                var: self.var(a.ident(id)),
                iterable: c[0],
                body: c[1],
            },
            L::ForAwaitOf { id, .. } => View::ForAwaitOf {
                var: self.var(a.ident(id)),
                iterable: c[0],
                body: c[1],
            },
            L::Assign { id, .. } => View::Assign {
                var: self.var(a.ident(id)),
                value: c[0],
            },
        };
        // A legacy DAG can bind an identifier in more than one branch. Bir has
        // one binder per variable; do not turn that representational gap into a panic.
        let bound: SmallVec<[VarId; 4]> = match view {
            View::Let { var, .. }
            | View::Try { exception: var, .. }
            | View::For { var, .. }
            | View::ForOf { var, .. }
            | View::ForAwaitOf { var, .. } => smallvec![var],
            View::Fun { header, .. } => self.bir.function(header).params.iter().collect(),
            View::Catch { header, .. } => self.bir.catch(header).params.iter().collect(),
            View::LetRec { first, values, .. } => (0..values.len())
                .map(|i| VarId(first.0 + index(i)))
                .collect(),
            _ => SmallVec::new(),
        };
        if bound.iter().any(|v| self.bir.vars.binder(*v).is_some()) {
            return Err(Unsupported("multiply bound identifier"));
        }
        Ok(self.bir.new_node(view, aux))
    }
}

pub(super) fn children(a: &LamArena, node: L) -> SmallVec<[Lam; 4]> {
    match node {
        L::Var(_) | L::GlobalModule(_) | L::Const(_) | L::Break | L::Continue => SmallVec::new(),
        L::Apply { func, args, .. } => std::iter::once(func)
            .chain(a.list(args).iter().copied())
            .collect(),
        L::Function { body, .. } => smallvec![body],
        L::Let { value, body, .. } => smallvec![value, body],
        L::LetRec { values, body, .. } => a
            .list(values)
            .iter()
            .copied()
            .chain(std::iter::once(body))
            .collect(),
        L::Prim { args, .. } | L::StaticRaise { args, .. } => SmallVec::from_slice(a.list(args)),
        L::Switch { scrut, actions, .. } | L::StringSwitch { scrut, actions, .. } => {
            std::iter::once(scrut)
                .chain(a.list(actions).iter().copied())
                .collect()
        }
        L::StaticCatch { body, handler, .. } | L::TryWith { body, handler, .. } => {
            smallvec![body, handler]
        }
        L::TryFinally { body, finally } => smallvec![body, finally],
        L::If { cond, then_, else_ } => smallvec![cond, then_, else_],
        L::Sequence(a, b) | L::While(a, b) => smallvec![a, b],
        L::For { kids, .. } => SmallVec::from_slice(a.list(kids)),
        L::ForOf { iter, body, .. } | L::ForAwaitOf { iter, body, .. } => smallvec![iter, body],
        L::Assign { value, .. } => smallvec![value],
    }
}

/// Memoized bottom-up binder facts. Each reachable source node is decoded
/// once; the expansion walk only reads these facts, never scans a subtree.
fn sharing_facts(arena: &LamArena, root: Lam) -> (Vec<u8>, usize, u8) {
    enum Work { Enter(Lam), Finish(Lam, L) }
    let mut state = vec![0u8; arena.node_count()];
    let mut binder = vec![0u8; arena.node_count()];
    let mut shared = 0u8;
    let mut labels = crate::fast_hash::AHashSet::new();
    let mut reachable = 0;
    let mut work = vec![Work::Enter(root)];
    while let Some(task) = work.pop() {
        match task {
            Work::Enter(id) => {
                if state[id.index()] == 2 { shared |= binder[id.index()]; continue; }
                assert_eq!(state[id.index()], 0, "cyclic Lambda arena");
                state[id.index()] = 1;
                reachable += 1;
                let node = arena.node(id);
                if let L::StaticCatch { info, .. } = node {
                    if !labels.insert(arena.catch_payload(info).label) { shared |= 4; }
                }
                work.push(Work::Finish(id, node));
                work.extend(children(arena, node).into_iter().rev().map(Work::Enter));
            }
            Work::Finish(id, node) => {
                let local = match node {
                    L::Let { .. } | L::LetRec { .. } | L::TryWith { .. }
                    | L::For { .. } | L::ForOf { .. } | L::ForAwaitOf { .. } => 1,
                    L::Function { info, .. } => u8::from(!arena.params(info).is_empty()),
                    L::StaticCatch { info, .. } => 2 | u8::from(!arena.idents(arena.catch_payload(info).params).is_empty()),
                    L::Var(_) | L::GlobalModule(_) | L::Const(_) | L::Break | L::Continue
                    | L::Apply { .. } | L::Prim { .. } | L::Switch { .. } | L::StringSwitch { .. }
                    | L::StaticRaise { .. } | L::TryFinally { .. } | L::If { .. }
                    | L::Sequence(..) | L::While(..) | L::Assign { .. } => 0,
                };
                binder[id.index()] = children(arena, node).into_iter().fold(local, |bits, c| bits | binder[c.index()]);
                state[id.index()] = 2;
            }
        }
    }
    (binder, reachable, shared)
}

/// Import occurrences, as the legacy lowering does. Binder-free shared
/// subtrees are copied per edge, with a hard budget of four times the reachable
/// source nodes. Repeated binder subtrees cannot retain unique Bir binders.
pub fn import_lambda(arena: &LamArena, root: Lam) -> Result<Imported, Unsupported> {
    import_with_sharing(arena, root, false).0
}

/// Same import, with the subset of binder fallbacks due solely to catch labels.
/// The binder analysis runs once, also when the import is unsupported.
pub(crate) fn import_for_lowering(arena: &LamArena, root: Lam) -> (Result<Imported, Unsupported>, bool) {
    import_with_sharing(arena, root, true)
}

fn import_with_sharing(arena: &LamArena, root: Lam, lowering: bool) -> (Result<Imported, Unsupported>, bool) {
    let (binders, reachable, shared) = sharing_facts(arena, root);
    let catch_only = shared != 0 && shared & 1 == 0;
    let result = if shared == 4 && !lowering {
        // Earlier round oracles retain their established label-shadowing reason.
        Err(Unsupported("reused static catch label"))
    } else if shared != 0 {
        Err(Unsupported("shared Lambda subtree with binder"))
    } else {
        import_with_facts(arena, root, &binders, reachable)
    };
    (result, catch_only)
}

fn import_with_facts(arena: &LamArena, root: Lam, has_binder: &[u8], reachable: usize) -> Result<Imported, Unsupported> {
    enum Work {
        Enter(Lam),
        Finish(L, usize),
    }
    let mut importer = Importer::default();
    importer.bir.begin_bulk();
    let mut work = vec![Work::Enter(root)];
    let mut values = Vec::new();
    let mut seen = vec![false; arena.node_count()];
    let budget = reachable.saturating_mul(4);
    let mut occurrences = 0;
    while let Some(task) = work.pop() {
        match task {
            Work::Enter(id) => {
                if std::mem::replace(&mut seen[id.index()], true) && has_binder[id.index()] != 0 {
                    return Err(Unsupported("shared Lambda subtree with binder"));
                }
                occurrences += 1;
                if occurrences > budget {
                    return Err(Unsupported("shared Lambda expansion"));
                }
                let node = arena.node(id);
                importer.binders(arena, node)?;
                let children = children(arena, node);
                let count = children.len();
                work.push(Work::Finish(node, count));
                work.extend(children.into_iter().rev().map(Work::Enter));
            }
            Work::Finish(node, count) => {
                let start = values.len() - count;
                let result = importer.node(arena, node, &values[start..])?;
                values.truncate(start);
                values.push(result);
            }
        }
    }
    let root = values[0];
    importer.bir.try_finish_bulk(root)?;
    Ok(Imported {
        arena: importer.bir,
        root,
        idents: importer.idents,
        globals: importer.globals,
        labels: Default::default(),
        #[cfg(test)]
        identifier_lookups: importer.identifier_lookups,
    })
}

/// Import a Lambda fragment (a function inlined from another module) into an
/// arena that already holds a unit. Its identifiers get fresh variables,
/// appended to `foreign` in allocation order; `globals` is the unit's module
/// table, extended in step with the arena's imports. The fragment is a
/// detached tree. Cost: one visit and one allocation per source node.
pub(super) fn import_fragment(
    bir: &mut Bir,
    globals: &mut Vec<Ident>,
    foreign: &mut Vec<Ident>,
    arena: &LamArena,
    root: Lam,
) -> Result<NodeId, Unsupported> {
    enum Work {
        Enter(Lam),
        Finish(L, usize),
    }
    let mut importer = Importer {
        bir: std::mem::take(bir),
        globals: std::mem::take(globals),
        ..Importer::default()
    };
    let mut work = vec![Work::Enter(root)];
    let mut values = Vec::new();
    let mut result = Ok(());
    while let Some(task) = work.pop() {
        match task {
            Work::Enter(id) => {
                let node = arena.node(id);
                if let Err(reason) = importer.binders(arena, node) {
                    result = Err(reason);
                    break;
                }
                let children = children(arena, node);
                work.push(Work::Finish(node, children.len()));
                work.extend(children.into_iter().rev().map(Work::Enter));
            }
            Work::Finish(node, count) => {
                let start = values.len() - count;
                match importer.node(arena, node, &values[start..]) {
                    Ok(built) => {
                        values.truncate(start);
                        values.push(built);
                    }
                    Err(reason) => {
                        result = Err(reason);
                        break;
                    }
                }
            }
        }
    }
    *bir = importer.bir;
    *globals = importer.globals;
    foreign.extend(importer.idents);
    result.map(|()| values[0])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn imports_a_hundred_thousand_nodes_linearly() {
        let mut a = LamArena::new();
        let mut root = a.const_(C::JsNull);
        for _ in 0..49_999 {
            let value = a.const_(C::JsNull);
            root = a.seq_raw(value, root);
        }
        root = a.prim_raw(
            crate::lambda::lam_primitive::Primitive::Pignore,
            &[root],
            crate::lambda::LamLoc::NONE,
        );
        assert_eq!(a.node_count(), 100_000);
        let imported = import_lambda(&a, root).unwrap();
        let steps = imported.arena.steps.get();
        println!("import 100000 nodes: {steps} steps");
        assert!(steps < 40 * 100_000, "{steps}");
        imported.arena.validate(Some(imported.root), false).unwrap();
    }

    #[test]
    fn hundred_thousand_variable_uses_need_only_identifier_lookups() {
        let mut a = LamArena::new();
        let x = Ident::create_local("x");
        let mut root = a.var(x);
        for _ in 1..100_000 {
            let value = a.var(x);
            root = a.seq_raw(value, root);
        }
        let imported = import_lambda(&a, root).unwrap();
        assert_eq!(imported.identifier_lookups, 100_000);
        assert_eq!(imported.arena.vars.uses(VarId(0)), 100_000);
        assert!(imported.arena.steps.get() < 40 * a.node_count() as u64);
        // Count accumulation is indexed by VarId in try_adjust_direct; the
        // only importer hash table touched per use is Importer::vars.
    }

    #[test]
    fn simplify_lets_creates_shared_constant_occurrences() {
        let mut a = LamArena::new();
        let id = Ident::new("x", 1, crate::ident::IdentFlags::NONE);
        let f = Ident::new("f", 2, crate::ident::IdentFlags::NONE);
        let value = a.const_(C::Int { i: 42, comment: None });
        let callee = a.var(f);
        let x = a.var(id);
        let y = a.var(id);
        let call = a.apply_raw(callee, &[x, y], crate::lambda::ApInfo { loc: crate::lambda::LamLoc::NONE, status: crate::lambda::ApplyStatus::Na });
        let root = a.let_(LetKind::Alias, id, value, call);
        import_lambda(&a, root).unwrap();
        let root = crate::lambda::lam_pass_lets_dce::simplify_lets(&mut a, root);
        let L::Apply { args, .. } = a.node(root) else { panic!("expected call") };
        assert_eq!(a.list(args)[0], a.list(args)[1]);
        import_lambda(&a, root).unwrap();
    }

    #[test]
    fn shared_constant_occurrences_round_trip() {
        let mut a = LamArena::new();
        let c = a.const_(C::JsNull);
        let root = a.seq_raw(c, c);
        let imported = import_lambda(&a, root).unwrap();
        let exported = export_lambda(&imported).unwrap();
        let mut before = Vec::new();
        let mut after = Vec::new();
        crate::lambda::sexp_lambda::print_lambda(&a.export(root), &mut before).unwrap();
        crate::lambda::sexp_lambda::print_lambda(&exported.to_tree(), &mut after).unwrap();
        assert_eq!(before, after);
    }

    #[test]
    fn constant_shared_by_ten_thousand_parents_is_linear() {
        let mut a = LamArena::new();
        let c = a.const_(C::JsNull);
        let mut root = a.const_(C::JsNull);
        for _ in 0..10_000 { root = a.seq_raw(c, root); }
        let (_, visits, _) = sharing_facts(&a, root);
        assert_eq!(visits, 10_002);
        let imported = import_lambda(&a, root).unwrap();
        assert_eq!(imported.arena.nodes.len(), 20_001);
        assert!(imported.arena.steps.get() < 40 * 20_001);
        imported.arena.validate(Some(imported.root), false).unwrap();
    }

    #[test]
    fn exponential_shared_chain_hits_expansion_budget() {
        let mut a = LamArena::new();
        let mut root = a.const_(C::JsNull);
        for _ in 0..30 { root = a.seq_raw(root, root); }
        let (_, visits, _) = sharing_facts(&a, root);
        assert_eq!(visits, 31);
        assert!(matches!(import_lambda(&a, root), Err(Unsupported("shared Lambda expansion"))));
    }

    #[test]
    fn shared_parameterless_catch_is_a_binder_fallback() {
        let mut a = LamArena::new();
        let body = a.static_raise(1, &[]);
        let handler = a.const_(C::JsNull);
        let catch = a.static_catch(body, 1, &[], handler);
        let root = a.seq_raw(catch, catch);
        let (binders, _, shared) = sharing_facts(&a, root);
        assert_eq!(binders[catch.index()], 2, "catch label, no handler parameters");
        assert_eq!(shared, 2);
        let (result, catch_only) = import_for_lowering(&a, root);
        assert!(catch_only);
        assert!(matches!(result, Err(Unsupported("shared Lambda subtree with binder"))));
    }

    #[test]
    fn rebuilt_catches_sharing_a_label_are_catch_only_binders() {
        let mut a = LamArena::new();
        let body = a.static_raise(1, &[]);
        let handler = a.const_(C::JsNull);
        let first = a.static_catch(body, 1, &[], handler);
        let body = a.static_raise(1, &[]);
        let handler = a.const_(C::JsNull);
        let second = a.static_catch(body, 1, &[], handler);
        let root = a.seq_raw(first, second);
        let (result, catch_only) = import_for_lowering(&a, root);
        assert!(catch_only);
        assert!(matches!(result, Err(Unsupported("shared Lambda subtree with binder"))));
    }

    #[test]
    fn shared_subtree_with_let_is_unsupported() {
        let mut a = LamArena::new();
        let id = Ident::new("x", 1, crate::ident::IdentFlags::NONE);
        let value = a.const_(C::JsNull);
        let body = a.var(id);
        let binding = a.let_(LetKind::Strict, id, value, body);
        let root = a.seq_raw(binding, binding);
        assert!(matches!(import_lambda(&a, root), Err(Unsupported("shared Lambda subtree with binder"))));
    }

    #[test]
    fn invalid_spelling_falls_back() {
        let mut a = LamArena::new();
        let root = a.const_(C::Float("not a float".into()));
        assert!(matches!(
            import_lambda(&a, root),
            Err(Unsupported("invalid float constant spelling"))
        ));
    }
}

pub(super) fn export_constant(b: &Bir, root: ConstId) -> Result<C, Unsupported> {
    enum Work {
        Enter(ConstId),
        Finish(ConstId, usize),
    }
    let mut work = vec![Work::Enter(root)];
    let mut values = Vec::new();
    while let Some(task) = work.pop() {
        let (id, count) = match task {
            Work::Enter(id) => {
                let children = match b.constant(id) {
                    Constant::Block { fields, .. } => b.constant_fields(*fields),
                    Constant::Some(inner) => std::slice::from_ref(inner),
                    _ => &[],
                };
                work.push(Work::Finish(id, children.len()));
                work.extend(children.iter().rev().copied().map(Work::Enter));
                continue;
            }
            Work::Finish(id, count) => (id, count),
        };
        let start = values.len() - count;
        let c = match b.constant(id) {
            Constant::Null => C::JsNull,
            Constant::Undefined(is_unit) => C::JsUndefined { is_unit: *is_unit },
            Constant::Bool(true) => C::JsTrue,
            Constant::Bool(false) => C::JsFalse,
            Constant::Int(i) => C::Int {
                i: i32::try_from(*i).map_err(|_| Unsupported("integer outside i32"))?,
                comment: None,
            },
            Constant::NativeInt(i) => C::NativeInt {
                i: *i,
                comment: None,
            },
            Constant::DecoratedInt {
                value,
                native,
                comment,
            } => {
                let comment = Some(Box::new(comment.clone()));
                if *native {
                    C::NativeInt { i: *value, comment }
                } else {
                    C::Int {
                        i: i32::try_from(*value).map_err(|_| Unsupported("integer outside i32"))?,
                        comment,
                    }
                }
            }
            Constant::Constructor(tag) => C::Constructor(tag.clone()),
            Constant::Char(c) => C::Char(*c as i32),
            Constant::String(s) => C::String(b.text(*s).to_owned()),
            Constant::ImmString(s) => C::ImmString(b.text(*s).to_owned()),
            Constant::Pointer(s) => C::Pointer(b.text(*s).to_owned()),
            Constant::Float(f) => C::Float(b.text(f.spelling()).to_owned()),
            Constant::BigInt(s) => {
                let s = b.text(*s);
                let (sign, value) = s.split_at_checked(1).ok_or(Unsupported("bigint sign"))?;
                if !matches!(sign, "+" | "-") {
                    return Err(Unsupported("bigint sign"));
                }
                C::BigInt {
                    negative: sign == "-",
                    value: value.to_owned(),
                }
            }
            Constant::Block { tag, .. } => C::Block {
                tag_info: Box::new(tag.clone()),
                elements: values.drain(start..).collect(),
            },
            Constant::Some(_) => C::Some(Box::new(values.pop().unwrap())),
            Constant::ModuleAlias => C::ModuleAlias,
        };
        values.truncate(start);
        values.push(c);
    }
    Ok(values.pop().unwrap())
}

impl Imported {
    /// Register a round-created rename, in creation order. The variable's
    /// explicit order is the stamp allocated from the round's private counter;
    /// the imported source supplies its name and flags. Amortized O(1), with
    /// no access to the legacy counter and no change to imported identities.
    pub fn register_rename(&mut self, var: VarId, source: VarId) -> Result<(), Unsupported> {
        if var.index() != self.idents.len() {
            return Err(Unsupported("fresh identities registered out of order"));
        }
        let source = self.ident(source)?;
        if self.arena.vars().name(var) != source.name_atom() {
            return Err(Unsupported("fresh identity is not a rename"));
        }
        self.idents.push(Ident::new(
            source.name_atom(),
            self.arena.vars().order(var) as i32,
            source.flags(),
        ));
        Ok(())
    }

    /// Register a variable the host imported with a fragment, in creation
    /// order, under the identity it has in the module it came from.
    pub(super) fn register_foreign(&mut self, var: VarId, ident: Ident) -> Result<(), Unsupported> {
        if var.index() != self.idents.len() {
            return Err(Unsupported("fresh identities registered out of order"));
        }
        self.idents.push(ident);
        Ok(())
    }

    /// Register a static label a round created as a copy of `source`: the
    /// legacy passes keep the label of a handler they copy, so the export
    /// prints the copy under the label of its origin.
    pub fn register_label(&mut self, fresh: u32, source: u32) {
        let legacy = self.labels.get(&source).copied().unwrap_or(source);
        self.labels.insert(fresh, legacy);
    }

    fn label(&self, label: u32) -> i32 {
        self.labels.get(&label).copied().unwrap_or(label) as i32
    }

    /// The unit's module table, for a host that imports fragments.
    pub(super) fn globals(&self) -> &[Ident] {
        &self.globals
    }

    /// Replace the module table by the one a host extended.
    pub(super) fn set_globals(&mut self, globals: Vec<Ident>) {
        debug_assert!(globals.starts_with(&self.globals));
        self.globals = globals;
    }

    /// The legacy identity of every variable, by variable.
    pub(super) fn idents(&self) -> &[Ident] {
        &self.idents
    }

    pub(super) fn ident(&self, var: VarId) -> Result<Ident, Unsupported> {
        self.idents
            .get(var.index())
            .copied()
            .ok_or(Unsupported("variable without legacy identity"))
    }
    fn export_node(
        &self,
        a: &mut LamArena,
        view: View<'_>,
        aux: u16,
        c: &[Lam],
    ) -> Result<Lam, Unsupported> {
        let b = &self.arena;
        Ok(match view {
            View::Var { var } => a.var(self.ident(var)?),
            View::Global { module } => a.global_module(
                *self
                    .globals
                    .get(module.index())
                    .ok_or(Unsupported("module without legacy identity"))?,
            ),
            View::Const { value } => a.const_(export_constant(b, value)?),
            View::Apply { info, .. } => a.apply_raw(c[0], &c[1..], b.application(info).clone()),
            View::Fun { header, .. } => {
                let h = b.function(header);
                let params: Vec<_> = h
                    .params
                    .iter()
                    .map(|v| self.ident(v))
                    .collect::<Result<_, _>>()?;
                let params = a.add_idents(&params);
                let info = a.add_func(
                    i32::from(aux),
                    params,
                    b.function_attributes(header).clone(),
                    h.loc,
                );
                a.function_with(info, c[0])
            }
            View::Let { var, value, .. } => {
                if value.is_none() {
                    return Err(Unsupported("released let value"));
                }
                let kind = match aux {
                    0 => LetKind::Strict,
                    1 => LetKind::Alias,
                    2 => LetKind::StrictOpt,
                    3 => LetKind::Variable,
                    _ => return Err(Unsupported("unknown let kind")),
                };
                a.let_(kind, self.ident(var)?, c[0], c[1])
            }
            View::LetRec { first, values, .. } => {
                let pairs: Vec<_> = c[..values.len()]
                    .iter()
                    .enumerate()
                    .map(|(i, &value)| self.ident(VarId(first.0 + index(i))).map(|id| (id, value)))
                    .collect::<Result<_, _>>()?;
                a.letrec(&pairs, c[values.len()])
            }
            View::Prim { primitive, .. } => {
                let p = b.primitive(primitive);
                a.prim_raw(p.primitive.clone(), c, p.loc)
            }
            View::Switch { header, .. } => {
                let h = b.switch(header);
                let keys: Vec<_> = h
                    .keys
                    .iter()
                    .map(|key| match key {
                        CaseKey::Lambda(key) => Ok(key.clone()),
                        _ => Err(Unsupported("non-Lambda switch key")),
                    })
                    .collect::<Result<_, _>>()?;
                let info = a.add_switch(
                    h.consts_full,
                    keys[..h.constants as usize].iter().cloned(),
                    h.blocks_full,
                    keys[h.constants as usize..].iter().cloned(),
                    h.has_default,
                    h.dispatch.clone(),
                );
                let actions = a.add_list(&c[1..]);
                a.switch_raw(c[0], actions, info)
            }
            View::StrSwitch { header, .. } => {
                let h = b.switch(header);
                let keys: Vec<_> = h
                    .keys
                    .iter()
                    .map(|key| match key {
                        CaseKey::String(key) => Ok(b.text(*key)),
                        _ => Err(Unsupported("non-string switch key")),
                    })
                    .collect::<Result<_, _>>()?;
                let info = a.add_str_switch(keys, h.has_default);
                let actions = a.add_list(&c[1..]);
                a.string_switch_raw(c[0], actions, info)
            }
            View::Exit { label, .. } => a.static_raise(self.label(label), c),
            View::Catch { header, .. } => {
                let h = b.catch(header);
                let params: Vec<_> = h
                    .params
                    .iter()
                    .map(|v| self.ident(v))
                    .collect::<Result<_, _>>()?;
                a.static_catch(c[0], self.label(h.label), &params, c[1])
            }
            View::Try { exception, .. } => a.try_(c[0], self.ident(exception)?, c[1]),
            View::TryFinally { .. } => a.try_finally(c[0], c[1]),
            View::If { .. } => a.if_raw(c[0], c[1], c[2]),
            View::Seq { .. } => a.seq_raw(c[0], c[1]),
            View::While { .. } => a.while_(c[0], c[1]),
            View::For { var, .. } => a.for_(
                self.ident(var)?,
                c[0],
                c[1],
                match aux {
                    0 => DirectionFlag::Upto,
                    1 => DirectionFlag::Downto,
                    _ => return Err(Unsupported("unknown for direction")),
                },
                c[2],
            ),
            View::ForOf { var, .. } => a.for_of(self.ident(var)?, c[0], c[1]),
            View::ForAwaitOf { var, .. } => a.for_await_of(self.ident(var)?, c[0], c[1]),
            View::Assign { var, .. } => a.assign(self.ident(var)?, c[0]),
            View::Break => a.break_(),
            View::Continue => a.continue_(),
            _ => return Err(Unsupported("JS-level node in Lambda export")),
        })
    }
}

/// Export without running Lambda smart-constructor rewrites or changing the
/// legacy identifier counter. Each Bir node is decoded once.
pub fn export_lambda(program: &Imported) -> Result<LamProgram, Unsupported> {
    enum Work<'a> {
        Enter(NodeId),
        Finish(View<'a>, u16, usize),
    }
    let b = &program.arena;
    let mut a = LamArena::new();
    let mut work = vec![Work::Enter(program.root)];
    let mut values = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            Work::Enter(id) => {
                let node = b.node(id);
                let view = node.view(&b.lists);
                let children = view.children();
                work.push(Work::Finish(view, node.aux(), children.len()));
                work.extend(children.into_iter().rev().map(Work::Enter));
            }
            Work::Finish(view, aux, count) => {
                let start = values.len() - count;
                let result = program.export_node(&mut a, view, aux, &values[start..])?;
                values.truncate(start);
                values.push(result);
            }
        }
    }
    Ok(LamProgram {
        arena: a,
        root: values[0],
    })
}

#[cfg(test)]
mod roundtrip_tests {
    use super::*;

    fn identity(a: &LamArena, root: Lam) {
        let imported = import_lambda(a, root).unwrap();
        imported.arena.validate(Some(imported.root), false).unwrap();
        let exported = export_lambda(&imported).unwrap();
        let mut before = Vec::new();
        let mut after = Vec::new();
        crate::lambda::sexp_lambda::print_lambda(&a.export(root), &mut before).unwrap();
        crate::lambda::sexp_lambda::print_lambda(&exported.to_tree(), &mut after).unwrap();
        assert_eq!(
            String::from_utf8(before).unwrap(),
            String::from_utf8(after).unwrap()
        );
    }

    #[test]
    fn round_created_renames_preserve_names_flags_and_stamp_order() {
        let source = Ident::new("temporary", 40, crate::ident::IdentFlags::NONE);
        let mut a = LamArena::new();
        let root = a.var(source);
        let mut imported = import_lambda(&a, root).unwrap();
        let View::Var { var: original } = imported.arena.view(imported.root) else {
            panic!("expected variable");
        };
        let generator = crate::context::IdGenerator::new();
        generator.set_current_stamp(100);
        for stamp in [101, 102] {
            let fresh = imported.arena.new_var_id(source.name_atom(), stamp);
            assert!(imported.ident(fresh).is_err());
            imported.register_rename(fresh, original).unwrap();
            assert_eq!(imported.ident(fresh).unwrap(), source.rename(&generator));
            assert_eq!(imported.ident(original).unwrap(), source);
        }
    }

    #[test]
    fn float_spellings_round_trip_including_nested_blocks() {
        for spelling in [
            "1.",
            "1.0",
            "1e0",
            "0x1p0",
            "1.00",
            "-0.",
            "-0.0",
            "infinity",
            "-infinity",
            "nan",
            "-nan",
            "Infinity",
            "-Infinity",
            "NaN",
            "1e999",
            "-1e999",
        ] {
            let mut a = LamArena::new();
            let root = a.const_(C::Float(spelling.into()));
            identity(&a, root);
            let nested = C::Block {
                tag_info: Box::new(crate::lambda::lam_tag_info::TagInfo::Tuple),
                elements: vec![C::Some(Box::new(C::Block {
                    tag_info: Box::new(crate::lambda::lam_tag_info::TagInfo::Tuple),
                    elements: vec![C::Float(spelling.into())],
                }))],
            };
            let root = a.const_(nested);
            identity(&a, root);
        }
    }

    #[test]
    fn equal_float_values_keep_distinct_pool_entries() {
        let mut b = Bir::default();
        let mut ids = Vec::new();
        for spelling in ["1.", "1.0", "1e0", "0x1p0", "1.00"] {
            let id = b.intern_float(spelling).unwrap();
            assert!(!ids.contains(&id));
            assert_eq!(id, b.intern_float(spelling).unwrap());
            let Constant::Float(f) = b.constant(id) else {
                panic!("not a float")
            };
            assert_eq!(f.value(), 1.0);
            assert_eq!(b.text(f.spelling()), spelling);
            ids.push(id);
        }
        let id = b.intern_float("-0.").unwrap();
        let Constant::Float(f) = b.constant(id) else {
            panic!("not a float")
        };
        assert_eq!(f.value().to_bits(), (-0.0f64).to_bits());
    }

    #[test]
    fn identity_retains_constants_and_binder_metadata() {
        for value in [
            C::JsNull,
            C::JsUndefined { is_unit: true },
            C::JsTrue,
            C::JsFalse,
            C::Int {
                i: -3,
                comment: Some(Box::new(
                    crate::lambda::lam_constant::PointerInfo::ShapeNone,
                )),
            },
            C::NativeInt {
                i: i64::MIN,
                comment: None,
            },
            C::Char(97),
            C::String("a\0b".into()),
            C::ImmString("immutable".into()),
            C::BigInt {
                negative: true,
                value: "000".into(),
            },
            C::Some(Box::new(C::JsNull)),
            C::Pointer("tag".into()),
            C::ModuleAlias,
        ] {
            let mut a = LamArena::new();
            let root = a.const_(value);
            identity(&a, root);
        }
        let mut a = LamArena::new();
        let p = Ident::create_local("param");
        let f = Ident::create_local("f");
        let body = a.var(p);
        let params = a.add_idents(&[p]);
        let h = a.add_func(
            1,
            params,
            crate::lambda::FunctionAttribute::default(),
            crate::lambda::LamLoc::NONE,
        );
        let fun = a.function_with(h, body);
        let body = a.var(f);
        let root = a.letrec(&[(f, fun)], body);
        identity(&a, root);
    }

    #[test]
    fn identity_retains_static_catches_loops_and_switches() {
        let mut a = LamArena::new();
        let p = Ident::create_local("caught");
        let arg = a.const_(C::int(42));
        let body = a.static_raise(7, &[arg]);
        let handler = a.var(p);
        let caught = a.static_catch(body, 7, &[p], handler);
        let scrutinee = a.const_(C::int(0));
        let info = a.add_switch(false, [], false, [], true, SwitchDispatch::Direct);
        let actions = a.add_list(&[caught]);
        let switch = a.switch_raw(scrutinee, actions, info);
        let cond = a.const_(C::JsFalse);
        let root = a.while_(cond, switch);
        identity(&a, root);

        let mut a = LamArena::new();
        let i = Ident::create_local("i");
        let start = a.const_(C::int(10));
        let end = a.const_(C::int(0));
        let body = a.var(i);
        let root = a.for_(i, start, end, DirectionFlag::Downto, body);
        identity(&a, root);
    }
}

/// The JS-level bridge is explicitly unfinished. No opaque legacy tree is
/// smuggled into Bir, and callers must keep using the legacy JS arena.
pub fn import_js(_program: &crate::js_ir::arena::JsProgram) -> Result<Imported, Unsupported> {
    Err(Unsupported("JS arena import not implemented"))
}

#[cfg(test)]
mod fallback_tests {
    use super::*;

    #[test]
    fn excessive_default_weight_is_unsupported_not_a_panic() {
        let mut a = LamArena::new();
        let mut root = a.const_(C::JsNull);
        for _ in 0..32 {
            let scrut = a.const_(C::int(0));
            let info = a.add_switch(false, [], false, [], true, SwitchDispatch::Direct);
            let actions = a.add_list(&[root]);
            root = a.switch_raw(scrut, actions, info);
        }
        assert!(matches!(
            import_lambda(&a, root),
            Err(Unsupported("use weight outside u32"))
        ));
    }

    #[test]
    fn excessive_weighted_variable_count_is_unsupported_not_a_panic() {
        let mut a = LamArena::new();
        let x = Ident::create_local("x");
        let left = a.var(x);
        let right = a.var(x);
        let mut root = a.seq_raw(left, right);
        // Each use fits u32 (2^31), but their sum does not.
        for _ in 0..31 {
            let scrut = a.const_(C::int(0));
            let info = a.add_switch(false, [], false, [], true, SwitchDispatch::Direct);
            let actions = a.add_list(&[root]);
            root = a.switch_raw(scrut, actions, info);
        }
        assert!(matches!(
            import_lambda(&a, root),
            Err(Unsupported("use count outside u32"))
        ));
    }

    #[test]
    fn excessive_weighted_exit_count_is_unsupported_not_a_panic() {
        let mut a = LamArena::new();
        let left = a.static_raise(7, &[]);
        let right = a.static_raise(7, &[]);
        let mut body = a.seq_raw(left, right);
        for _ in 0..31 {
            let scrut = a.const_(C::int(0));
            let info = a.add_switch(false, [], false, [], true, SwitchDispatch::Direct);
            let actions = a.add_list(&[body]);
            body = a.switch_raw(scrut, actions, info);
        }
        let handler = a.const_(C::JsNull);
        let root = a.static_catch(body, 7, &[], handler);
        assert!(matches!(
            import_lambda(&a, root),
            Err(Unsupported("use count outside u32"))
        ));
    }

    #[test]
    fn js_import_is_an_explicit_fallback() {
        let program = crate::js_ir::arena::JsProgram::new_in(
            vec![],
            vec![],
            crate::js_ir::arena::JsArena::new(),
        );
        assert!(matches!(
            import_js(&program),
            Err(Unsupported("JS arena import not implemented"))
        ));
    }
}
