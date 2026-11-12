//! `Lam_pass_remove_alias.simplify_alias` on the rewrite engine
//! (`lambda/lam_pass_remove_alias.rs`, compiler/core/lam_pass_remove_alias.ml):
//! field reads of known blocks, optional unwrapping, boolean folding and the
//! inlining of applications (`bir/l/beta.rs`).
//!
//! What the pass knows about a binder is what `Lam_pass_collect.collect_info`
//! recorded before it ran (BACKEND_REDESIGN.md C.2 row 1). Here that is the
//! fact the arena maintains, frozen when the round starts, and read through
//! [`Table::entry`], which turns it into the legacy table's entry the first
//! time it is asked for, or when the sweep reaches the binding, whichever
//! comes first. Nothing below a binding has been edited at either moment, so
//! the entry describes the binding as it was when the round started. The
//! entries are a dense table indexed by variable; block elements are in one
//! pool. No hash table is involved.
//!
//! Costs. The sweep enters a node once (subtrees without an application, a
//! primitive, a conditional or a string switch are not entered), an entry is
//! built once (constant time, or the number of fields of a block) and read in
//! constant time. A function that may be inlined is copied once, before the
//! first edit inside it, and only then (`Engine::guard_enter`). An inlined
//! application costs the analyses and the copy of the body (`beta.rs`).
use crate::bir::engine::Engine;
use crate::bir::*;
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_primitive::Primitive;

/// `Lam_compile_context.rec_flag` of a bound function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Rec {
    /// Bound by `let`.
    NonRec,
    /// The only binding of a `let rec`.
    SelfRec,
    /// One of several bindings of a `let rec`.
    Rec,
}

/// A simple expression a fact names (`Lam_util.element_of_lambda`,
/// lam_pass_collect.rs:19-33), by value: the node it was read from may be
/// rewritten later in the sweep.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Elem {
    /// Not a simple form.
    Na,
    /// A variable.
    Var(VarId),
    /// A constant.
    Const(ConstId),
    /// A module field of a module.
    FieldOfGlobal(PrimId, ImportId),
    /// A module field of a variable.
    FieldOfVar(PrimId, VarId),
}

/// `Lam_id_kind.t` as the pass reads it (`lam_stats.rs`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Entry {
    /// Not asked for yet.
    Unset,
    /// No entry. Also what the pass makes of an entry it does not read: a
    /// mutable block, an exported binding that is not a function.
    Na,
    /// `Parameter`: a function parameter.
    Param,
    /// `Constant`.
    Const(ConstId),
    /// `Module`.
    Module(ImportId),
    /// `Normal_optional`: `Some(x)`, with `x` when it is a variable or a
    /// constant.
    Optional(Elem),
    /// `OptionalBlock`: a nullable conversion of a variable.
    Nullable(VarId, BoxedNullable),
    /// `ImmutableBlock`: elements `start..start + len` of the pool.
    Block {
        /// First element.
        start: u32,
        /// Number of elements.
        len: u32,
    },
    /// `FunctionId` whose definition is a function.
    Function {
        /// The function node.
        node: NodeId,
        /// How it is bound.
        rec: Rec,
        /// [`may_be_inlined`] of the function as it was when the round
        /// started. A function that fails it is never inlined, so the round
        /// keeps no copy of it; it must not be inlined either when the sweep
        /// has since made it small.
        inlinable: bool,
    },
}

/// A necessary condition of `beta::ok_to_inline` that does not read the
/// arguments: which bound functions a round must be able to read as they
/// were when it started (BACKEND_REDESIGN.md C.2 row 1).
fn may_be_inlined(b: &Bir, function: NodeId) -> bool {
    use crate::lambda::InlineAttribute;
    let View::Fun { body, header } = b.view(function) else {
        return false;
    };
    let attr = b.function_attributes(header);
    if !crate::lambda::lam_analysis::attr_can_be_inlined(attr) {
        return false;
    }
    if attr.is_a_functor {
        return true;
    }
    match attr.inline {
        InlineAttribute::Always => true,
        InlineAttribute::Never => false,
        InlineAttribute::Default => {
            let params = b.function(header).params;
            let on_param = |n: NodeId| {
                matches!(b.view(n), View::Var { var } if params.iter().any(|p| p == var))
            };
            super::exits::size_upto(b, body, 10) < 10
                || match b.view(body) {
                    View::Switch { scrutinee, .. } => on_param(scrutinee),
                    View::If { condition, .. } => on_param(condition),
                    _ => false,
                }
        }
    }
}

/// The legacy identifier table, built on demand from the frozen facts.
#[derive(Default)]
pub(crate) struct Table {
    entries: Vec<Entry>,
    elems: Vec<Elem>,
    /// Variables from here on were created by the round: they have the
    /// entries the round registers and no other.
    fresh_from: usize,
}

/// `Lam_util.element_of_lambda` (lam_pass_collect.rs:19-33, lam_util.ml:188-196).
fn element(b: &Bir, n: NodeId) -> Elem {
    match b.view(n) {
        View::Var { var } => Elem::Var(var),
        View::Const { value } => Elem::Const(value),
        View::Prim {
            args: [x],
            primitive,
        } if matches!(
            b.primitive(primitive).primitive,
            Primitive::Pfield(_, FieldDbgInfo::Module { .. })
        ) =>
        {
            match b.view(*x) {
                View::Global { module } => Elem::FieldOfGlobal(primitive, module),
                View::Var { var } => Elem::FieldOfVar(primitive, var),
                _ => Elem::Na,
            }
        }
        _ => Elem::Na,
    }
}

impl Table {
    /// A table for a round over `e`'s unit, empty.
    pub(crate) fn new(e: &Engine<'_>) -> Self {
        Self {
            entries: Vec::new(),
            elems: Vec::new(),
            fresh_from: e.bir().vars().len(),
        }
    }

    fn set(&mut self, var: VarId, entry: Entry) {
        if self.entries.len() <= var.index() {
            self.entries.resize(var.index() + 1, Entry::Unset);
        }
        self.entries[var.index()] = entry;
    }

    /// `Lam_util.kind_of_lambda_block` (lam_pass_collect.rs:36-38).
    fn block(&mut self, b: &Bir, args: &[NodeId]) -> Entry {
        let start = self.elems.len() as u32;
        self.elems.extend(args.iter().map(|x| element(b, *x)));
        Entry::Block {
            start,
            len: args.len() as u32,
        }
    }

    /// The elements of a block entry.
    pub(crate) fn elements(&self, start: u32, len: u32) -> &[Elem] {
        &self.elems[start as usize..(start + len) as usize]
    }

    /// `Lam_pass_collect.collect_bind` (lam_pass_collect.rs:323-380,
    /// lam_pass_collect.ml:58-93) for one binder, from its maintained fact.
    /// Where the fact and the legacy entry differ by design:
    /// - a mutable block has a fact and no entry (lam_pass_collect.rs:331
    ///   matches immutable blocks only);
    /// - a nullable conversion has an entry only when its operand is a
    ///   variable (lam_pass_collect.rs:345);
    /// - the parameters of a static handler have the fact `Param` and no
    ///   entry (`Collector::params` runs for functions only);
    /// - an alias has the fact `Alias(y)` and the entry of `y`
    ///   (`alias_ident_or_global`, lam_pass_collect.rs:41-52).
    fn build(&mut self, e: &Engine<'_>, var: VarId) -> Entry {
        let b = e.bir();
        match e.fact(var) {
            Fact::Unknown | Fact::MutableBlock(_) => Entry::Na,
            // Followed by `entry`.
            Fact::Alias(_) => Entry::Na,
            Fact::Param => match b.vars().binder(var).map(|n| b.node(n).op()) {
                Some(Op::Fun) => Entry::Param,
                _ => Entry::Na,
            },
            Fact::Const(c) => Entry::Const(c),
            Fact::Module(m) => Entry::Module(ImportId(m)),
            Fact::Block(node) => match b.view(node) {
                View::Prim { args, .. } => {
                    let args: smallvec::SmallVec<[NodeId; 8]> = args.into();
                    self.block(b, &args)
                }
                _ => Entry::Na,
            },
            Fact::Optional(x) => Entry::Optional(match element(b, x) {
                simple @ (Elem::Var(_) | Elem::Const(_)) => simple,
                _ => Elem::Na,
            }),
            Fact::NullableOptional(x, kind) => match b.view(x) {
                View::Var { var } => Entry::Nullable(var, kind),
                _ => Entry::Na,
            },
            Fact::Function { node, rec } => Entry::Function {
                node,
                inlinable: may_be_inlined(b, node),
                rec: match rec {
                    RecFlag::No => Rec::NonRec,
                    RecFlag::Yes => match b.vars().binder(var).map(|n| b.view(n)) {
                        Some(View::LetRec { values, .. }) if values.len() == 1 => Rec::SelfRec,
                        _ => Rec::Rec,
                    },
                },
            },
        }
    }

    /// The entry of `var`. An alias has the entry of what it names; a chain
    /// of aliases is followed once and every link remembers the result.
    pub(crate) fn entry(&mut self, e: &Engine<'_>, var: VarId) -> Entry {
        let known = |table: &Self, var: VarId| {
            table
                .entries
                .get(var.index())
                .copied()
                .filter(|entry| *entry != Entry::Unset)
        };
        if let Some(entry) = known(self, var) {
            return entry;
        }
        let mut chain: smallvec::SmallVec<[VarId; 4]> = smallvec::SmallVec::new();
        let mut at = var;
        let entry = loop {
            if let Some(entry) = known(self, at) {
                break entry;
            }
            if at.index() >= self.fresh_from {
                break Entry::Na;
            }
            chain.push(at);
            match e.fact(at) {
                Fact::Alias(target) => at = target,
                _ => break self.build(e, at),
            }
        };
        for link in chain {
            self.set(link, entry);
        }
        entry
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::bridge::import_lambda;
    use crate::bir::engine::testing::{call, id, prim};
    use crate::lambda::arena::LamArena;
    use crate::lambda::lam_compat::LetKind;
    use crate::lambda::lam_constant::Constant as C;
    use crate::lambda::lam_primitive::Mutable;
    use crate::lambda::lam_tag_info::TagInfo;

    /// Where the maintained fact and the legacy entry differ by design
    /// (`Table::build`): the fact exists, the legacy table has no entry.
    #[test]
    fn facts_the_legacy_table_does_not_hold() {
        let mut a = LamArena::new();
        let (m, n, h, x) = (id("m", 1), id("n", 2), id("h", 3), id("x", 4));
        let vx = a.var(x);
        let mutable = prim(
            &mut a,
            Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Mutable),
            &[vx],
        );
        let effect = call(&mut a, "effect", 5);
        let nullable = prim(&mut a, Primitive::PnullToOpt, &[effect]);
        let one = a.const_(C::int(1));
        let raise = a.static_raise(1, &[one]);
        let vh = a.var(h);
        let caught = a.static_catch(raise, 1, &[h], vh);
        let inner = a.let_(LetKind::Strict, n, nullable, caught);
        let root = a.let_(LetKind::Strict, m, mutable, inner);
        let tree = a.export(root);
        let mut a = LamArena::new();
        let root = a.import(&tree);
        let mut imported = import_lambda(&a, root).unwrap();
        let mut meta = crate::lambda::lam_stats::LamStats::new(vec![]);
        crate::lambda::lam_pass_collect::collect_info(&a, &mut meta, root);
        assert!(meta.ident_tbl.get(&m).is_none());
        assert!(meta.ident_tbl.get(&n).is_none());
        assert!(meta.ident_tbl.get(&h).is_none());
        let e = Engine::new(&mut imported.arena);
        let vars = e.bir().vars().len() as u32;
        let facts: Vec<Fact> = (0..vars).map(|i| e.bir().vars().fact(VarId(i))).collect();
        assert!(facts.iter().any(|f| matches!(f, Fact::MutableBlock(_))));
        assert!(facts.iter().any(|f| matches!(f, Fact::NullableOptional(..))));
        assert!(facts.iter().any(|f| matches!(f, Fact::Param)));
        let mut table = Table::new(&e);
        for i in 0..vars {
            assert_eq!(table.entry(&e, VarId(i)), Entry::Na);
        }
    }
}
