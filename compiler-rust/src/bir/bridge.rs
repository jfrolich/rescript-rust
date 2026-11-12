//! Migration bridges. Source nodes are decoded once, with explicit postorder
//! stacks rather than recursive arena exports. The identity side tables preserve
//! legacy identifier flags/stamps without allocating from the legacy counter.
use super::*;
use crate::fast_hash::AHashMap;
use crate::ident::Ident;
use crate::lambda::SwitchDispatch;
use crate::lambda::arena::{Lam, LamArena, Node as L};
use crate::lambda::lam_constant::Constant as C;
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
    idents: Vec<Ident>,
    globals: Vec<Ident>,
}

#[derive(Default)]
struct Importer {
    bir: Bir,
    vars: AHashMap<Ident, VarId>,
    idents: Vec<Ident>,
    globals: Vec<Ident>,
}
impl Importer {
    fn var(&mut self, ident: Ident) -> VarId {
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
    fn binders(&mut self, arena: &LamArena, node: L) -> Result<(), Unsupported> {
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
                // Bir stores IEEE bits, whereas sexp_lambda preserves spelling.
                C::Float(_) => return Err(Unsupported("float constant spelling")),
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
    fn node(&mut self, a: &LamArena, node: L, c: &[NodeId]) -> Result<NodeId, Unsupported> {
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

fn children(a: &LamArena, node: L) -> SmallVec<[Lam; 4]> {
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

/// Import the reachable program. A shared source node is a fallback: expanding
/// a DAG into a tree can be exponential in source node count. Each source node
/// is looked up at most once, even on that fallback path.
pub fn import_lambda(arena: &LamArena, root: Lam) -> Result<Imported, Unsupported> {
    enum Work {
        Enter(Lam),
        Finish(L, usize),
    }
    let mut importer = Importer::default();
    importer.bir.begin_bulk();
    let mut work = vec![Work::Enter(root)];
    let mut values = Vec::new();
    let mut seen = vec![false; arena.node_count()];
    while let Some(task) = work.pop() {
        match task {
            Work::Enter(id) => {
                if std::mem::replace(&mut seen[id.index()], true) {
                    return Err(Unsupported("shared Lambda node"));
                }
                let node = arena.node(id);
                importer.binders(arena, node)?;
                let children = children(arena, node);
                work.push(Work::Finish(node, children.len()));
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
    importer.bir.finish_bulk(root);
    Ok(Imported {
        arena: importer.bir,
        root,
        idents: importer.idents,
        globals: importer.globals,
    })
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
    fn shared_nodes_fall_back_without_expansion() {
        let mut a = LamArena::new();
        let c = a.const_(C::JsNull);
        let root = a.seq_raw(c, c);
        assert!(matches!(
            import_lambda(&a, root),
            Err(Unsupported("shared Lambda node"))
        ));
    }

    #[test]
    fn spelling_not_representable_falls_back() {
        let mut a = LamArena::new();
        let root = a.const_(C::Float("1.00".into()));
        assert!(matches!(
            import_lambda(&a, root),
            Err(Unsupported("float constant spelling"))
        ));
    }
}
