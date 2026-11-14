//! All tree mutations and the incremental maintenance they require.
use super::*;
use crate::lambda::lam_primitive::Primitive;
use smallvec::{SmallVec, smallvec};
use std::collections::HashMap;

/// Dense arena handles provide the index; only touched rows are cleared.
pub(super) trait DenseKey: Copy { fn slot(self) -> usize; }
macro_rules! dense_keys { ($($key:ty),*) => {$(
    impl DenseKey for $key { fn slot(self) -> usize { self.index() } }
)*}; }
dense_keys!(NodeId, VarId, FuncId, CatchId, JsId);

/// O(1) indexed lookup; O(touched rows) clearing; amortized growth by arena index.
pub(super) struct DenseMap<K> { rows: Vec<Option<K>>, touched: Vec<usize> }
impl<K> Default for DenseMap<K> {
    fn default() -> Self { Self { rows: Vec::new(), touched: Vec::new() } }
}
impl<K: DenseKey> DenseMap<K> {
    fn clear(&mut self) { for slot in self.touched.drain(..) { self.rows[slot] = None; } }
    pub(super) fn get(&self, key: &K) -> Option<&K> { self.rows.get(key.slot()).and_then(Option::as_ref) }
    pub(super) fn insert(&mut self, key: K, value: K) {
        let slot=key.slot();
        if slot >= self.rows.len() { self.rows.resize(slot+1,None); }
        if self.rows[slot].replace(value).is_none() { self.touched.push(slot); }
    }
    fn extend(&mut self, entries: impl IntoIterator<Item=(K,K)>) {
        for (key,value) in entries { self.insert(key,value); }
    }
    #[cfg(test)]
    fn capacity(&self) -> usize { self.rows.capacity() }
    fn reserve_domain(&mut self, slots: usize) { self.rows.reserve(slots.saturating_sub(self.rows.len())); }
}
impl<K: DenseKey> std::ops::Index<&K> for DenseMap<K> {
    type Output=K;
    fn index(&self,key:&K)->&K { self.get(key).expect("unmapped arena handle") }
}

/// Retained traversal and renaming storage for repeated subtree copies.
/// Clearing a copy preserves every buffer's high-water capacity.
#[derive(Default)]
pub(crate) struct CopyScratch {
    order: Vec<NodeId>,
    stack: Vec<NodeId>,
    vars: DenseMap<VarId>,
    funcs: DenseMap<FuncId>,
    catches: DenseMap<CatchId>,
    /// Source static labels are sparse numeric identities, not arena indices.
    labels: HashMap<u32, u32>,
    js: DenseMap<JsId>,
    nodes: DenseMap<NodeId>,
}

#[cfg(test)]
impl CopyScratch {
    /// Reserve the already reserved arena domains; recycled handles may change
    /// which row a second pass visits without increasing the arena's size.
    pub(crate) fn reserve_arena(&mut self, b: &Bir) {
        self.vars.reserve_domain(b.vars.name.capacity());
        self.funcs.reserve_domain(b.vars.funcs.capacity());
        self.catches.reserve_domain(b.pools.catches.capacity());
        self.js.reserve_domain(b.pools.js.capacity());
        self.nodes.reserve_domain(b.nodes.capacity());
    }
    pub(crate) fn capacities(&self) -> [usize; 13] {
        [self.order.capacity(), self.stack.capacity(), self.vars.capacity(), self.funcs.capacity(),
            self.catches.capacity(), self.labels.capacity(), self.js.capacity(), self.nodes.capacity(),
         self.vars.touched.capacity(), self.funcs.touched.capacity(), self.catches.touched.capacity(),
         self.js.touched.capacity(), self.nodes.touched.capacity()]
    }
}

#[derive(Clone, Copy)]
pub(super) enum BinderRun {
    Empty,
    One(Option<VarId>),
    Vars(VarSpan),
    Params(VarSpan),
    Rest(VarId, RestSpan),
}
impl BinderRun {
    pub(super) fn len(self) -> usize {
        match self {
            Self::Empty => 0,
            Self::One(_) => 1,
            Self::Vars(s) | Self::Params(s) => s.len(),
            Self::Rest(_, s) => 1 + s.len as usize,
        }
    }
    pub(super) fn at(self, b: &Bir, slot: usize) -> Option<VarId> {
        match self {
            Self::Empty => None,
            Self::One(v) => v,
            Self::Vars(s) => Some(VarId(s.start + index(slot))),
            Self::Params(s) => Some(b.vars.function_params[s.start as usize + slot]),
            Self::Rest(v, _) if slot == 0 => Some(v),
            Self::Rest(_, s) => b.rest_fields(s)[slot - 1].binding,
        }
    }
}

impl Bir {
    /// Construct an operation without rewrite rules. Children must be distinct,
    /// detached live roots. `aux` carries the operation's small enum/arity payload.
    /// No child handles may be shared, including through different list entries.
    pub fn new_node(&mut self, view: View<'_>, aux: u16) -> NodeId {
        self.new_node_in(view, aux, 1)
    }

    /// Attach a finalized lowering statement list without copying its elements
    /// a second time. O(statements), plus any changed use-weight recounts
    /// outside bulk construction. Each detached statement is adopted once.
    pub(crate) fn block_from_list(&mut self, list: ListId) -> NodeId {
        self.attach_list(Node::block_list(list), list)
    }

    /// O(actions): adopt a scrutinee and a finalized pooled action list once.
    pub(crate) fn switch_from_list(
        &mut self,
        scrutinee: NodeId,
        actions: ListId,
        header: SwitchId,
        aux: u16,
    ) -> NodeId {
        assert!(
            self.parents[scrutinee.index()].is_none(),
            "scrutinee already attached"
        );
        if !self.bulk {
            let weight = self.weight(scrutinee);
            if weight != 1 {
                self.adjust_counts(scrutinee, 1 - i64::from(weight));
            }
        }
        let id = self.attach_list(Node::switch_list(scrutinee, actions, header, aux), actions);
        self.parents[scrutinee.index()] = Some(id);
        id
    }

    /// O(arguments): adopt the callee and a pooled argument list exactly once.
    /// `None` selects construction; `Some` carries ordinary call metadata.
    pub(crate) fn call_from_list(
        &mut self,
        callee: NodeId,
        args: ListId,
        info: Option<JsId>,
    ) -> NodeId {
        assert!(
            self.parents[callee.index()].is_none(),
            "callee already attached"
        );
        if !self.bulk {
            let weight = self.weight(callee);
            if weight != 1 {
                self.adjust_counts(callee, 1 - i64::from(weight));
            }
        }
        let id = self.attach_list(Node::call_list(callee, args, info), args);
        self.parents[callee.index()] = Some(id);
        id
    }

    /// O(fields): adopt an object's pooled operands without a temporary vector.
    /// Each operand is adopted once; cached J facts inspect immediate children.
    pub(crate) fn object_from_list(&mut self, list: ListId, keys: PropertySpan) -> NodeId {
        assert_eq!(self.lists.get(list).len(), keys.len as usize);
        let info = self.js_info(JsPayload::Object(keys));
        let id = self.attach_list(Node::object_list(list, info), list);
        if j::facts::delay_safe(self, id) {
            let mut flags = self.node(id).flags();
            flags.0 |= NodeFlags::DELAY_SAFE;
            self.nodes[id.index()].set_flags(flags);
        }
        id
    }

    /// O(operands): adopt a finalized JSX list without a temporary operand vector.
    pub(crate) fn jsx_from_list(&mut self, list: ListId, header: JsxHeader, children: bool) -> NodeId {
        assert_eq!(self.lists.get(list).len(), 2 + usize::from(header.spread)
            + header.props.len as usize + header.children as usize + usize::from(header.key));
        let info = self.js_info(JsPayload::Jsx(header));
        self.attach_list(Node::jsx_list(list, info, u16::from(children)), list)
    }

    /// [`Self::block_from_list`] for an explicit block statement (B:1225).
    pub(crate) fn explicit_block_from_list(&mut self, list: ListId) -> NodeId {
        self.attach_list(Node::explicit_block_list(list), list)
    }

    fn attach_list(&mut self, node: Node, list: ListId) -> NodeId {
        let id = self.allocate(node);
        for i in 0..self.lists.get(list).len() {
            let child = self.lists.get(list)[i];
            self.node(child);
            assert!(self.parents[child.index()].is_none(), "statement already attached");
            if !self.bulk {
                let weight = self.weight(child);
                if weight != 1 {
                    self.adjust_counts(child, 1 - i64::from(weight));
                }
            }
            self.parents[child.index()] = Some(id);
        }
        self.repair(id);
        id
    }

    /// [`Self::new_node`] for a root that will fill a slot of use weight
    /// `weight` ([`Self::weight_of`] of the slot). Children that already carry
    /// the weight the new node gives them (see [`Self::detach`]) are attached
    /// without a walk; a child of another weight has its uses recounted.
    pub fn new_node_in(&mut self, view: View<'_>, aux: u16, weight: u32) -> NodeId {
        if let View::Var { var } = view {
            assert!(
                !self
                    .vars
                    .binder(var)
                    .is_some_and(|b| self.node(b).flags().contains(NodeFlags::DEAD)),
                "cannot reference a released dead binding"
            );
        }
        #[cfg(debug_assertions)]
        {
            if self.child_epoch == u32::MAX {
                self.checked_children.fill(0);
                self.child_epoch = 0;
            }
            self.child_epoch += 1;
            self.checked_children.resize(self.nodes.len(), 0);
        }
        for i in 0..view.child_count() {
            let child = view.child_at(i);
            #[cfg(debug_assertions)]
            {
                assert_ne!(self.checked_children[child.index()], self.child_epoch, "shared child");
                self.checked_children[child.index()] = self.child_epoch;
            }
            self.node(child);
            debug_assert!(self.parents[child.index()].is_none(), "child already attached");
        }
        let packed = Node::pack(view, aux, &mut self.lists);
        let id = self.allocate(packed);
        self.check_shape(id);
        self.bind(id);
        for i in 0..view.child_count() {
            let child = view.child_at(i);
            debug_assert!(self.parents[child.index()].is_none(), "shared child");
            if !self.bulk {
                // Read before linking: a detached root reports the weight it carries.
                let have = self.weight(child);
                let want = weight
                    .checked_mul(self.edge_weight(id, child))
                    .expect("Bir use weight overflow");
                if have != want {
                    self.adjust_counts(child, i64::from(want) - i64::from(have));
                }
            }
            self.parents[child.index()] = Some(id);
        }
        if !self.bulk {
            if weight != 1 {
                self.weights[id.index()] = weight;
            }
            self.adjust_direct(id, i64::from(weight));
        }
        self.repair(id);
        if !self.bulk {
            self.capture_created(id);
        }
        id
    }

    /// Defer capture analysis while constructing a complete tree. Do not edit or
    /// query capture flags until `finish_bulk`; the arena must be fresh.
    /// Weighted uses are finalized in the same pass.
    pub fn begin_bulk(&mut self) {
        assert!(!self.bulk, "bulk construction already active");
        assert!(self.nodes.is_empty(), "bulk construction needs a fresh arena");
        self.bulk = true;
    }

    /// Finish bulk construction with one top-down capture analysis. Existing
    /// conservative flags are retained, just as in incremental construction.
    pub fn finish_bulk(&mut self, root: NodeId) {
        self.try_finish_bulk(root).expect("Bir bulk count overflow");
    }

    /// Finish an imported tree, reporting unrepresentable weighted counts.
    /// On error the partially finalized arena must be discarded.
    pub fn try_finish_bulk(&mut self, root: NodeId) -> Result<(), bridge::Unsupported> {
        assert!(self.bulk, "bulk construction not active");
        self.mark_captures(root)?;
        self.bulk = false;
        Ok(())
    }

    fn mark_captures(&mut self, root: NodeId) -> Result<(), bridge::Unsupported> {
        let epoch = self.next_capture_epoch();
        // The completed arena already supplies a bound on pending children.
        // Reserve once rather than reallocating on wide completed units.
        let mut stack = Vec::with_capacity(self.nodes.len());
        stack.push((root, 0u32, 1u32));
        while let Some((id, depth, weight)) = stack.pop() {
            let view = self.view(id);
            let children = view.child_count();
            let boundary = match view {
                View::Fun { .. } | View::JFun { .. }
                | View::While { .. } | View::SWhile { .. } => Some(None),
                View::For { parts, .. } | View::SForRange { parts, .. } => {
                    Some(parts.last().copied())
                }
                _ => None,
            };
            let used_var = match view { View::Var { var } => Some(var), _ => None };
            // Parameters and loop variables are bound *inside* their own
            // capture boundary, not in the enclosing function's scope.
            let binder_depth = depth + u32::from(boundary.is_some());
            let run = self.binder_run(id);
            for slot in 0..run.len() {
                let Some(var) = run.at(self, slot) else { continue };
                self.bulk_binders[var.index()] = (epoch, binder_depth);
            }
            if let Some(var) = used_var {
                let (seen, bound_depth) = self.bulk_binders[var.index()];
                if depth != 0 && (seen != epoch || bound_depth < depth) {
                    self.vars.flags[var.index()].0 |= VarFlags::CAPTURED;
                }
            }
            self.weights[id.index()] = weight;
            self.try_adjust_direct(id, i64::from(weight))?;
            for index in (0..children).rev() {
                // Capture accounting changes flags/counts, never child edges.
                let child = self.view(id).child_at(index);
                let enters = match boundary {
                    Some(None) => true,
                    Some(Some(body)) => body == child,
                    None => false,
                };
                let child_weight = weight.checked_mul(self.edge_weight(id, child))
                    .ok_or(bridge::Unsupported("use weight outside u32"))?;
                stack.push((child, depth + u32::from(enters), child_weight));
            }
        }
        Ok(())
    }

    fn allocate(&mut self, node: Node) -> NodeId {
        let id = self.allocate_slot(node);
        // The lowering's arena records where each reference is: a variable
        // (T4a) or an imported module (the naming log reads both at the
        // close of a function scope).
        match node.op() {
            Op::Var => {
                if let Some(scope) = &mut self.js_scope {
                    let View::Var { var } = node.view(&self.lists) else { unreachable!() };
                    let site = scope.site(var, id);
                    self.nodes[id.index()].set_site(site);
                }
            }
            Op::JQualified => {
                if let Some(scope) = &mut self.js_scope {
                    let site = scope.import_site(id);
                    self.nodes[id.index()].set_site(site);
                }
            }
            _ => {}
        }
        id
    }
    fn allocate_slot(&mut self, node: Node) -> NodeId {
        self.visit();
        self.register_kind(node, true);
        if let Some(id) = self.free_nodes.pop() {
            self.nodes[id.index()] = node;
            if id.index() < self.tail_candidates.len() {
                self.tail_candidates[id.index()] = Default::default();
                self.self_tail[id.index()] = false;
                self.loop_facts[id.index()] = Default::default();
            }
            self.parents[id.index()] = None;
            self.weights[id.index()] = 0;
            if !self.cold.is_empty() {
                self.cold[id.index()] = None;
            }
            id
        } else {
            let id = NodeId(index(self.nodes.len()));
            self.nodes.push(node);
            self.parents.push(None);
            self.weights.push(0);
            self.capture_chain.push((0, false));
            if !self.cold.is_empty() {
                self.cold.push(None);
            }
            id
        }
    }

    pub(super) fn check_shape(&self, id: NodeId) {
        match self.view(id) {
            View::For { parts, .. } => assert_eq!(parts.len(), 3),
            View::SForRange { parts, .. } => assert!((2..=3).contains(&parts.len())),
            View::STry { parts, exception } => {
                assert!((2..=3).contains(&parts.len()));
                assert!(exception.is_some() || parts.len() == 2);
            }
            View::SForOf { parts, .. } | View::SForAwaitOf { parts, .. } => {
                assert_eq!(parts.len(), 2)
            }
            View::Switch {
                actions, header, ..
            }
            | View::StrSwitch {
                actions, header, ..
            }
            | View::SSwitch {
                actions, header, ..
            } => {
                let h = self.switch(header);
                assert_eq!(actions.len(), h.keys.len() + usize::from(h.has_default));
            }
            View::Let { value: None, .. } => {
                assert!(self.node(id).flags().contains(NodeFlags::DEAD))
            }
            View::Var { var } | View::Assign { var, .. } => assert!(var.index() < self.vars.len()),
            View::Const { value } | View::JNumber { value } => {
                self.constant(value);
            }
            View::Prim { primitive, .. } => {
                assert!(primitive.index() < self.pools.prims.len());
            }
            View::Apply { info, .. } => {
                assert!(info.index() < self.pools.apply.len());
            }
            View::JCall { info, .. } => {
                assert!(matches!(self.pools.js[info.index()], JsPayload::Call(_)))
            }
            View::JObject { values, info } => {
                let JsPayload::Object(keys) = &self.pools.js[info.index()] else {
                    panic!("object needs property keys")
                };
                assert_eq!(values.len(), self.property_keys(*keys).len());
            }
            View::JBlockLit { info, .. } => {
                assert!(matches!(self.pools.js[info.index()], JsPayload::Block(_) | JsPayload::ConstantBlock(_)))
            }
            View::JJsx { values, info } => {
                let JsPayload::Jsx(h) = &self.pools.js[info.index()] else {
                    panic!("JSX needs shape metadata")
                };
                assert_eq!(
                    values.len(),
                    2 + usize::from(h.spread)
                        + h.props.len as usize
                        + h.children as usize
                        + usize::from(h.key)
                );
            }
            View::JTemplate { values, info } | View::JTagged { values, info, .. } => {
                let (JsPayload::Template(parts) | JsPayload::Tagged(parts)) =
                    &self.pools.js[info.index()]
                else {
                    panic!("template needs segments")
                };
                assert_eq!(self.template_parts(*parts).len(), values.len() + 1);
            }
            View::JRecordRest { info, .. } | View::SRest { info, .. } => {
                assert!(matches!(self.pools.js[info.index()], JsPayload::Rest(_)))
            }
            _ => {}
        }
    }

    /// Snapshot handles, not a materialized list of binders. The descriptor
    /// stays valid while fresh binders and metadata are appended to the arena.
    pub(super) fn binder_run(&self, id: NodeId) -> BinderRun {
        self.binders_in(self.view(id))
    }
    fn binders_in(&self, view: View<'_>) -> BinderRun {
        match view {
            View::Let { var, .. } | View::SDecl { var, .. } | View::For { var, .. }
            | View::ForOf { var, .. } | View::ForAwaitOf { var, .. }
            | View::SForRange { var, parts: [_, _, _], .. } | View::SForOf { var, .. }
            | View::SForAwaitOf { var, .. } => BinderRun::One(Some(var)),
            View::SRest { var, info, .. } => {
                let JsPayload::Rest(fields) = self.javascript(info) else { unreachable!() };
                BinderRun::Rest(var, *fields)
            }
            View::Try { exception, .. } => BinderRun::One(Some(exception)),
            View::STry { exception, .. } => BinderRun::One(exception),
            View::LetRec { first, values, .. } => BinderRun::Vars(VarSpan { start: first.0, len: index(values.len()) }),
            View::Fun { header, .. } | View::JFun { header, .. } => {
                let h = self.function(header);
                if h.flags & FuncHeader::INDIRECT_PARAMS != 0 { BinderRun::Params(h.params) }
                else { BinderRun::Vars(h.params) }
            }
            View::Catch { header, .. } => BinderRun::Vars(self.catch(header).params),
            _ => BinderRun::Empty,
        }
    }
    pub(super) fn binders(&self, id: NodeId) -> SmallVec<[VarId; 4]> {
        let run = self.binder_run(id);
        (0..run.len()).filter_map(|slot| run.at(self, slot)).collect()
    }
    fn bind(&mut self, id: NodeId) {
        if let View::Fun { header, .. } | View::JFun { header, .. } = self.view(id) {
            assert!(
                self.func_owners[header.index()].replace(id).is_none(),
                "function header already owned"
            );
        }
        // A function's parameters get their home where its scope closes.
        // The op is read from the table, not through `node`, which would
        // count a visit.
        let home = self.js_scope.is_some()
            && !matches!(self.nodes[id.index()].op(), Op::Fun | Op::JFun);
        let run = self.binder_run(id);
            for slot in 0..run.len() {
                let Some(var) = run.at(self, slot) else { continue };
            assert!(
                self.vars.binder[var.index()].is_none(),
                "variable already bound"
            );
            self.vars.binder[var.index()] = Some(id);
            if home && let Some(scope) = &mut self.js_scope {
                scope.names.bind(var);
            }
        }
        self.update_facts(id);
    }
    fn unbind(&mut self, id: NodeId) {
        if let View::Fun { header, .. } | View::JFun { header, .. } = self.view(id) {
            if self.func_owners[header.index()] == Some(id) {
                self.func_owners[header.index()] = None;
            }
        }
        let run = self.binder_run(id);
            for slot in 0..run.len() {
                let Some(var) = run.at(self, slot) else { continue };
            if self.vars.binder[var.index()] == Some(id) {
                self.vars.binder[var.index()] = None;
                self.vars.fact[var.index()] = Fact::Unknown;
            }
        }
    }
    pub(super) fn value_fact(&self, id: NodeId, rec: RecFlag) -> Fact {
        match self.view(id) {
            View::Var { var } => Fact::Alias(var),
            View::Const { value } | View::JNumber { value } => Fact::Const(value),
            View::Global { module } => Fact::Module(module.0),
            View::Fun { .. } | View::JFun { .. } => Fact::Function { node: id, rec },
            View::JOptional { value } => Fact::Optional(value),
            View::JBlockLit { .. } | View::JArray { .. } => {
                if self.node(id).aux() == 0 {
                    Fact::Block(id)
                } else {
                    Fact::MutableBlock(id)
                }
            }
            View::Prim { primitive, args } => {
                match &self.pools.prims[primitive.index()].primitive {
                    Primitive::Pmakeblock(_, mutable) => {
                        if matches!(mutable, crate::lambda::lam_primitive::Mutable::Immutable) {
                            Fact::Block(id)
                        } else {
                            Fact::MutableBlock(id)
                        }
                    }
                    Primitive::Psome | Primitive::PsomeNotNest if args.len() == 1 => {
                        Fact::Optional(args[0])
                    }
                    Primitive::PnullToOpt if args.len() == 1 => {
                        Fact::NullableOptional(args[0], BoxedNullable::Null)
                    }
                    Primitive::PnullUndefinedToOpt if args.len() == 1 => {
                        Fact::NullableOptional(args[0], BoxedNullable::Both)
                    }
                    _ => Fact::Unknown,
                }
            }
            _ => Fact::Unknown,
        }
    }
    pub(super) fn binding_facts(&self, id: NodeId) -> SmallVec<[(VarId, Fact); 4]> {
        match self.view(id) {
            View::Let { var, value, .. } | View::SDecl { var, value } => smallvec![(
                var,
                value.map_or(Fact::Unknown, |v| self.value_fact(v, RecFlag::No)),
            )],
            View::LetRec { first, values, .. } => values
                .iter()
                .enumerate()
                .map(|(i, &v)| (VarId(first.0 + index(i)), self.value_fact(v, RecFlag::Yes)))
                .collect(),
            View::Fun { .. } | View::JFun { .. } | View::Catch { .. } => self
                .binders(id)
                .into_iter()
                .map(|v| (v, Fact::Param))
                .collect(),
            _ => self
                .binders(id)
                .into_iter()
                .map(|v| (v, Fact::Unknown))
                .collect(),
        }
    }
    fn update_facts(&mut self, id: NodeId) -> bool {
        let mut changed = false;
        // Only the lowering arena consumes this J-only fact. L rewrite arenas
        // must not allocate or maintain an unused per-node J table.
        if self.js_scope.is_some() {
            let duplicable = j::facts::external_duplicable(self, id);
            if self.j_duplicable.len() <= id.index() { self.j_duplicable.resize(id.index() + 1, false); }
            changed = self.j_duplicable[id.index()] != duplicable;
            self.j_duplicable[id.index()] = duplicable;
        }
        let node = self.node(id);
        let view = node.view(&self.lists);
        let run = self.binders_in(view);
        for slot in 0..run.len() {
            let Some(var) = run.at(self, slot) else { continue };
            let fact = match view {
                View::Let { value, .. } | View::SDecl { value, .. } =>
                    value.map_or(Fact::Unknown, |v| self.value_fact(v, RecFlag::No)),
                View::LetRec { values, .. } => self.value_fact(values[slot], RecFlag::Yes),
                View::Fun { .. } | View::JFun { .. } | View::Catch { .. } => Fact::Param,
                _ => Fact::Unknown,
            };
            changed |= self.vars.fact[var.index()] != fact;
            self.vars.fact[var.index()] = fact;
            if matches!(fact, Fact::Module(_)) {
                self.vars.flags[var.index()].0 |= VarFlags::MODULE;
            }
            if fact == Fact::Param {
                self.vars.flags[var.index()].0 |= VarFlags::PARAM;
            }
        }
        if let View::Assign { var, .. } = self.view(id) {
            self.vars.flags[var.index()].0 |= VarFlags::ASSIGNED;
        }
        // The lowering's arena keeps `ASSIGNED` as level L recorded it
        // (C:404 `assignable`, the targets of L assignments): a result
        // temporary or handler parameter the lowering assigns stays
        // delay-safe (A:28), as it is for the legacy lowering.
        if self.js_scope.is_some() {
            return changed;
        }
        if let View::JBin { left, .. } = self.view(id) {
            if self.node(id).aux() == crate::js_ir::op::BinOp::Eq as u16 {
                if let View::Var { var } = self.view(left) {
                    self.vars.flags[var.index()].0 |= VarFlags::ASSIGNED;
                }
            }
        }
        changed
    }

    pub(super) fn edge_weight(&self, parent: NodeId, child: NodeId) -> u32 {
        if let View::Switch {
            actions, header, ..
        } = self.view(parent)
        {
            let h = self.switch(header);
            if h.has_default && !h.consts_full && !h.blocks_full && actions.last() == Some(&child) {
                return 2;
            }
        }
        1
    }
    pub(super) fn is_weighted_switch(&self, node: Node) -> bool {
        if let View::Switch { header, .. } = node.view(&self.lists) {
            let h = self.switch(header);
            h.has_default && !h.consts_full && !h.blocks_full
        } else {
            false
        }
    }
    pub(super) fn is_capture_kind(node: Node) -> bool {
        matches!(
            node.op(),
            Op::Fun | Op::JFun | Op::While | Op::SWhile | Op::For | Op::SForRange
        )
    }
    fn register_kind(&mut self, node: Node, add: bool) {
        if node.op() == Op::Var {
            if let Some(scope) = &mut self.js_scope {
                let View::Var { var } = node.view(&self.lists) else { unreachable!() };
                scope.occurrence(var, add);
                if !add {
                    scope.sites[node.site() as usize].node = NodeId(u32::MAX);
                }
            }
        }
        if node.op() == Op::JQualified {
            if let Some(scope) = &mut self.js_scope {
                let View::JQualified { module, .. } = node.view(&self.lists) else { unreachable!() };
                scope.import_reference(module, add);
                if !add {
                    scope.sites[node.site() as usize].node = NodeId(u32::MAX);
                }
            }
        }
        if self.is_weighted_switch(node) {
            if add {
                self.weighted_switches += 1;
            } else {
                self.weighted_switches -= 1;
            }
        }
        if Self::is_capture_kind(node) {
            if add {
                self.capture_boundaries += 1;
            } else {
                self.capture_boundaries -= 1;
            }
        }
    }
    fn weight(&mut self, mut id: NodeId) -> u32 {
        // Ordinary modules need no ancestor walk, however deep their Let spine.
        // A cached weight still wins: a detached root may carry the weight of
        // the slot it came from (`detach`).
        if self.weighted_switches == 0 && self.weights[id.index()] == 0 {
            return 1;
        }
        let requested = id;
        let mut path = std::mem::take(&mut self.weight_path);
        debug_assert!(path.is_empty());
        let mut weight;
        loop {
            self.visit();
            let cached = self.weights[id.index()];
            if cached != 0 {
                weight = cached;
                break;
            }
            if let Some(parent) = self.parents[id.index()] {
                path.push((id, self.edge_weight(parent, id)));
                id = parent;
            } else {
                self.weights[id.index()] = 1;
                weight = 1;
                break;
            }
        }
        for (id, multiplier) in path.drain(..).rev() {
            weight = weight
                .checked_mul(multiplier)
                .expect("Bir use weight overflow");
            self.weights[id.index()] = weight;
        }
        self.weight_path = path;
        debug_assert!(self.weights[requested.index()] != 0);
        weight
    }
    fn adjust_direct(&mut self, id: NodeId, delta: i64) {
        self.try_adjust_direct(id, delta)
            .expect("Bir use count overflow/underflow");
    }
    fn try_adjust_direct(&mut self, id: NodeId, delta: i64) -> Result<(), bridge::Unsupported> {
        match self.view(id) {
            View::Var { var } => {
                self.vars.uses[var.index()] =
                    u32::try_from(i64::from(self.vars.uses[var.index()]) + delta)
                        .map_err(|_| bridge::Unsupported("use count outside u32"))?;
                if delta < 0 && self.vars.uses(var) == 0 && !self.deaths_deferred {
                    if let Some(binder) = self.vars.binder(var) {
                        self.death_candidates.push(binder);
                    }
                }
            }
            View::Exit { label, .. } => {
                // Headers may be built before their handlers, but before their exits.
                let header_id = self
                    .pools
                    .catch_labels
                    .get(&label)
                    .expect("unknown static exit label");
                let header = &mut self.pools.catches[header_id.index()];
                header.uses = u32::try_from(i64::from(header.uses) + delta)
                    .map_err(|_| bridge::Unsupported("use count outside u32"))?;
            }
            _ => {}
        }
        Ok(())
    }
    fn adjust_counts(&mut self, root: NodeId, delta: i64) {
        let mut stack = std::mem::take(&mut self.count_stack);
        debug_assert!(stack.is_empty());
        stack.push((root, delta));
        while let Some((id, delta)) = stack.pop() {
            // This walk changes precisely the use weights of moved content or
            // a newly doubled default. All other cached paths stay valid.
            self.weights[id.index()] = 0;
            self.adjust_direct(id, delta);
            let view = self.view(id);
            for at in 0..view.child_count() {
                let child = view.child_at(at);
                stack.push((
                    child,
                    delta
                        .checked_mul(i64::from(self.edge_weight(id, child)))
                        .expect("Bir use weight overflow"),
                ));
            }
        }
        self.count_stack = stack;
    }

    pub(super) fn effects(
        &self,
        id: NodeId,
        child_effects: impl Fn(NodeId) -> (bool, bool),
    ) -> (bool, bool) {
        let view = self.view(id);
        let j_pure = j::facts::purity(self, id, false, |c| child_effects(c).0);
        let all_pure = (0..view.child_count()).all(|i| child_effects(view.child_at(i)).0);
        let no_alloc = (0..view.child_count()).all(|i| child_effects(view.child_at(i)).1);
        let effects = match view {
            View::Var { .. }
            | View::Global { .. }
            | View::JQualified { .. }
            | View::JNumber { .. }
            | View::JStr { .. }
            | View::JBool
            | View::JNull
            | View::JUndefined => (true, true),
            View::Const { value } => (
                true,
                !matches!(
                    self.constant(value),
                    Constant::Block { .. } | Constant::Some(_)
                ),
            ),
            View::Fun { .. } | View::JFun { .. } => (true, false),
            View::Prim { primitive, args } => {
                let p = &self.pools.prims[primitive.index()].primitive;
                let second = args.get(1).and_then(|&n| match self.view(n) {
                    View::Const { value } => match self.constant(value) {
                        Constant::Int(n) => {
                            Some(crate::lambda::lam_constant::Constant::NativeInt {
                                i: *n,
                                comment: None,
                            })
                        }
                        _ => None,
                    },
                    _ => None,
                });
                let pure = crate::lambda::lam_analysis::is_pure_primitive(p, second.as_ref());
                // Deliberately conservative: allocation-free primitives are a small whitelist.
                let alloc_free = matches!(
                    p,
                    Primitive::Pidentity
                        | Primitive::Pignore
                        | Primitive::Pnot
                        | Primitive::Paddint
                        | Primitive::Psubint
                        | Primitive::Pmulint
                        | Primitive::Pnegint
                );
                (all_pure && pure, no_alloc && alloc_free)
            }
            View::Let { .. }
            | View::LetRec { .. }
            | View::Try { .. }
            | View::TryFinally { .. }
            | View::If { .. }
            | View::Seq { .. }
            | View::JCond { .. }
            | View::JSeq { .. }
            | View::SBlock { .. }
            | View::SExp { .. }
            | View::SDecl { .. } => (all_pure, no_alloc),
            View::JArray { .. } | View::JBlockLit { .. } | View::JOptional { .. } => {
                (all_pure, false)
            }
            // Property access, coercions, proxies, calls and raw JS may run user code.
            _ => (false, false),
        };
        (j_pure.unwrap_or(effects.0), effects.1)
    }
    /// O(arity): compute L control facts in one immediate-child fold, including
    /// loop labels and tail candidates supplied by the construction callback.
    /// Fun is a control boundary (compiler/core/lam_exit_code.ml:28).
    pub(super) fn control_facts(
        &self,
        node: Node,
        mut child_facts: impl FnMut(NodeId) -> (NodeFlags, super::tail_facts::LoopFacts),
    ) -> (NodeFlags, super::tail_facts::LoopFacts) {
        use super::tail_facts::LoopFacts as L;
        let empty = L::default();
        let own = match node.op() {
            Op::Exit => return (NodeFlags(NodeFlags::HAS_EXIT | NodeFlags::HAS_STATEMENT), empty),
            Op::Fun | Op::Var => return (NodeFlags::default(), empty),
            Op::Break | Op::Continue => return (NodeFlags(NodeFlags::HAS_STATEMENT), L(L::JUMP)),
            Op::Switch | Op::StrSwitch | Op::Catch | Op::Try | Op::TryFinally | Op::While
            | Op::For | Op::ForOf | Op::ForAwaitOf | Op::Assign => true,
            op if op as u8 <= Op::Continue as u8 => false,
            _ => return (NodeFlags::default(), empty),
        };
        let view = node.view(&self.lists);
        let tail = match view {
            View::Const { value } => return (NodeFlags(if matches!(self.constant(value), Constant::Undefined(true)) {
                NodeFlags::TRIVIAL_UNIT
            } else { 0 }), empty),
            View::Seq { second, .. } => Some(second),
            View::Let { value: Some(_), body, .. } => Some(body),
            _ => None,
        };
        let loop_body = match view {
            View::While { body, .. }
            | View::ForOf { body, .. } | View::ForAwaitOf { body, .. } => Some(body),
            View::For { parts, .. } => parts.get(2).copied(),
            _ => None,
        };
        #[cfg(test)]
        if loop_body.is_some() { self.loop_fact_folds.set(self.loop_fact_folds.get() + 1); }
        let scrutinee = match view {
            View::Switch { scrutinee, .. } | View::StrSwitch { scrutinee, .. } => Some(scrutinee),
            _ => None,
        };
        let mut unit = tail.is_some();
        let both = NodeFlags::HAS_EXIT | NodeFlags::HAS_STATEMENT;
        let mut facts = NodeFlags(if own { NodeFlags::HAS_STATEMENT } else { 0 });
        let mut loops = empty;
        for at in 0..view.child_count() {
            let child = view.child_at(at);
            let (flags, jumps) = child_facts(child);
            facts.0 |= flags.0 & both;
            unit &= flags.contains(if tail == Some(child) { NodeFlags::TRIVIAL_UNIT } else { NodeFlags::PURE });
            if let Some(body) = loop_body {
                if body == child {
                    if jumps.0 & L::SWITCH_JUMP != 0 { loops.0 |= L::NEEDS_LABEL; }
                    if jumps.0 & L::JUMP != 0 { loops.0 |= L::BODY_JUMP; }
                } else {
                    // Bounds run outside the new frame. A while condition
                    // with statements runs inside its generated JS loop,
                    // so its outward jump crosses that loop (lam_compile.ml:1322).
                    loops.0 |= jumps.0 & (L::JUMP | L::SWITCH_JUMP);
                    if node.op() == Op::While && jumps.0 & L::JUMP != 0 { loops.0 |= L::SWITCH_JUMP; }
                }
            } else {
                loops.0 |= jumps.0 & (L::JUMP | L::SWITCH_JUMP);
                if scrutinee.is_some_and(|s| s != child) && jumps.0 & L::JUMP != 0 {
                    loops.0 |= L::SWITCH_JUMP;
                }
            }
        }
        if unit { facts.0 |= NodeFlags::TRIVIAL_UNIT; }
        (facts, loops)
    }
    /// O(affected ancestor edges and their direct operands); stops at an unchanged fact.
    fn repair(&mut self, id: NodeId) {
        self.repair_with_tail_child(id, None);
    }
    /// Same bound as repair, including changed tail-position edges whose list
    /// endpoints stayed fixed. A recursive binding also reads its tail candidates.
    fn repair_with_tail_child(&mut self, mut id: NodeId, mut changed_child: Option<NodeId>) {
        loop {
            let (pure, no_alloc) = self.effects(id, |c| {
                let f = self.node(c).flags();
                (f.contains(NodeFlags::PURE), f.contains(NodeFlags::NO_ALLOC))
            });
            let old_node = self.node(id);
            let (control, tail_changed) = self.repair_control_facts(id, changed_child);
            let old_flags = old_node.flags();
            let mut flags = old_flags;
            flags.0 &= !(NodeFlags::PURE | NodeFlags::NO_ALLOC);
            if old_node.op() != Op::Var && old_node.op() as u8 <= Op::Continue as u8 {
                flags.0 = (flags.0 & !NodeFlags::CONTROL) | control.0;
            }
            if pure {
                flags.0 |= NodeFlags::PURE;
            }
            if no_alloc {
                flags.0 |= NodeFlags::NO_ALLOC;
            }
            if !matches!(old_node.view(&self.lists), View::Var { .. }) {
                if let Some(strict) = j::facts::purity(self, id, true, |c| {
                    matches!(self.view(c), View::Var { .. }) || j::facts::strictly_pure(self, c)
                }) {
                    flags.0 &= !NodeFlags::STRICT;
                    if strict { flags.0 |= NodeFlags::STRICT; }
                    flags.0 &= !NodeFlags::J_SUBEXPR;
                    if j::facts::subexpression(self, id, |c| matches!(self.view(c), View::Var { .. }) || self.node(c).flags().contains(NodeFlags::J_SUBEXPR)) {
                        flags.0 |= NodeFlags::J_SUBEXPR;
                    }
                }
            }
            self.nodes[id.index()].set_flags(flags);
            let facts_changed = self.update_facts(id) || tail_changed;
            if flags == old_flags && !facts_changed {
                break;
            }
            changed_child = tail_changed.then_some(id);
            match self.parents[id.index()] {
                Some(parent) => id = parent,
                None => break,
            }
        }
    }
    pub(super) fn capture_boundary(&self, id: NodeId, child: NodeId) -> bool {
        match self.view(id) {
            View::Fun { .. } | View::JFun { .. } | View::While { .. } | View::SWhile { .. } => true,
            View::For { parts, .. } | View::SForRange { parts, .. } => parts.last() == Some(&child),
            _ => false,
        }
    }
    pub(super) fn is_descendant(&self, mut id: NodeId, ancestor: NodeId) -> bool {
        loop {
            self.visit();
            if id == ancestor {
                return true;
            }
            match self.parents[id.index()] {
                Some(parent) => id = parent,
                None => return false,
            }
        }
    }
    fn next_capture_epoch(&mut self) -> u64 {
        self.capture_epoch = self
            .capture_epoch
            .checked_add(1)
            .expect("capture epoch overflow");
        self.capture_epoch
    }
    // One tree walk records both binders and uses; the second loop touches only
    // variable IDs. Buffers and epoch columns survive calls, so no clearing pass.
    fn collect_capture(&mut self, root: NodeId, epoch: u64) {
        let mut stack = std::mem::take(&mut self.capture_stack);
        let mut uses = std::mem::take(&mut self.capture_uses);
        stack.clear();
        uses.clear();
        stack.push(root);
        while let Some(id) = stack.pop() {
            let run = self.binder_run(id);
            for slot in 0..run.len() {
                let Some(var) = run.at(self, slot) else { continue };
                self.capture_binders[var.index()] = epoch;
            }
            if let View::Var { var } = self.view(id) {
                uses.push(var);
            }
            stack.extend(self.view(id).children());
        }
        self.capture_stack = stack;
        self.capture_uses = uses;
    }
    fn capture_created(&mut self, id: NodeId) {
        let root = match self.view(id) {
            View::Fun { .. } | View::JFun { .. } | View::While { .. } | View::SWhile { .. } => id,
            View::For { parts, .. } | View::SForRange { parts, .. } => *parts.last().unwrap(),
            _ => return,
        };
        let epoch = self.next_capture_epoch();
        let run = self.binder_run(id);
            for slot in 0..run.len() {
                let Some(var) = run.at(self, slot) else { continue };
            self.capture_binders[var.index()] = epoch;
        }
        self.collect_capture(root, epoch);
        for &var in &self.capture_uses {
            if self.capture_binders[var.index()] != epoch {
                self.vars.flags[var.index()].0 |= VarFlags::CAPTURED;
            }
        }
    }
    fn capture_moved(&mut self, root: NodeId) {
        if self.capture_boundaries == 0 || self.parents[root.index()].is_none() {
            return;
        }
        let epoch = self.next_capture_epoch();
        self.collect_capture(root, epoch);
        if self.capture_uses.iter().all(|v| {
            self.capture_binders[v.index()] == epoch
                || self.vars.flags(*v).contains(VarFlags::CAPTURED)
        }) {
            return;
        }
        let mut child = root;
        let mut boundary = false;
        while let Some(parent) = self.parents[child.index()] {
            self.visit();
            // A binder on the boundary itself is inside its own scope.
            self.capture_chain[parent.index()] = (epoch, boundary);
            boundary |= self.capture_boundary(parent, child);
            child = parent;
        }
        if !boundary {
            return;
        }
        for &var in &self.capture_uses {
            if self.capture_binders[var.index()] == epoch {
                continue;
            }
            let captured = self.vars.binder(var).is_none_or(|binder| {
                let (seen, crossed) = self.capture_chain[binder.index()];
                seen != epoch || crossed
            });
            if captured {
                self.vars.flags[var.index()].0 |= VarFlags::CAPTURED;
            }
        }
    }

    /// Overwrite a live slot with a detached tree or a descendant of that slot.
    /// The replacement handle is invalid afterwards; the target handle survives.
    ///
    /// Cost: the removed nodes, plus the replacement's subtree when its use
    /// weight changes (it enters or leaves a doubled switch default) or, for a
    /// detached replacement in a unit with capture boundaries, one walk of it
    /// for the capture flags. [`Self::replace_local`] avoids the second walk.
    pub fn replace(&mut self, target: NodeId, replacement: NodeId) {
        assert_ne!(target, replacement);
        self.node(target);
        self.node(replacement);
        debug_assert!(
            self.parents[replacement.index()].is_none() || self.is_descendant(replacement, target),
            "replacement belongs to another tree"
        );
        debug_assert!(
            self.view(replacement).children().is_empty()
                || !self.is_descendant(target, replacement),
            "replacement creates a cycle"
        );
        self.replace_impl(target, replacement, false);
    }

    /// [`Self::replace`] for a rewrite that moves no variable use under a
    /// function or loop it was not under before: the replacement is a
    /// descendant of the target, or a detached tree built from nodes detached
    /// from the target's subtree and from new nodes without variable uses.
    /// Capture flags are then already right, so the cost is the removed nodes
    /// only, unless the kept content changes use weight.
    pub fn replace_local(&mut self, target: NodeId, replacement: NodeId) {
        assert_ne!(target, replacement);
        self.node(target);
        self.node(replacement);
        self.replace_impl(target, replacement, true);
    }

    fn replace_impl(&mut self, target: NodeId, replacement: NodeId, local: bool) {
        let descendant = self.parents[replacement.index()].is_some();
        let (target_weight, replacement_weight) = if self.bulk {
            (1, 1)
        } else {
            (self.weight(target), self.weight(replacement))
        };
        // Content that keeps its weight keeps every count and cached weight
        // below it: only a change of weight needs the two recounting walks.
        let recount = target_weight != replacement_weight;
        if recount {
            self.adjust_counts(replacement, -i64::from(replacement_weight));
        }
        let parent = self.parents[target.index()];
        // The two level-L control facts share their bits with level-J
        // metadata: a change of either re-derives the parent, which reads
        // them from its children.
        let effect_bits = NodeFlags::PURE | NodeFlags::NO_ALLOC | NodeFlags::STRICT
            | NodeFlags::J_SUBEXPR | NodeFlags::HAS_EXIT | NodeFlags::HAS_STATEMENT;
        let effects_before = self.nodes[target.index()].flags().0 & effect_bits;
        self.release_nodes(target, Some(replacement), false);
        let content = self.nodes[replacement.index()];
        let cold = self.cold.get(replacement.index()).copied().flatten();
        self.unbind(replacement);
        let tail_changed = if !self.tail_candidates.is_empty() {
            let before = self.tail_candidates[target.index()];
            let loop_changed = self.loop_facts[target.index()] != self.loop_facts[replacement.index()];
            self.loop_facts[target.index()] = self.loop_facts[replacement.index()];
            self.tail_candidates[target.index()] = self.tail_candidates[replacement.index()];
            self.self_tail[target.index()] = self.self_tail[replacement.index()];
            loop_changed || before != self.tail_candidates[target.index()]
                || parent.is_some_and(|parent| matches!(self.view(parent), View::Apply { callee, .. } if callee == target))
        } else { false };
        self.nodes[target.index()] = content;
        // A reference that moves into the slot takes its site with it.
        if matches!(content.op(), Op::Var | Op::JQualified) {
            if let Some(scope) = &mut self.js_scope {
                scope.sites[content.site() as usize].node = target;
            }
        }
        self.parents[target.index()] = parent;
        for child in self.view(target).children() {
            self.parents[child.index()] = Some(target);
        }
        self.nodes[replacement.index()] = Node::free();
        self.weights[replacement.index()] = 0;
        self.parents[replacement.index()] = None;
        self.free_nodes.push(replacement);
        if !self.cold.is_empty() {
            self.cold[target.index()] = cold;
            self.cold[replacement.index()] = None;
        }
        self.bind(target);
        if recount {
            self.adjust_counts(target, i64::from(target_weight));
        }
        if !self.bulk {
            // The slot keeps its parent edge and therefore its incoming weight,
            // even when its contents change kind. Descendant caches were cleared
            // by a recount; no node outside the replaced subtree changed weight.
            self.weights[target.index()] = target_weight;
        }
        self.repair(target);
        if let Some(parent) = parent {
            // The parent's effects read its children's two effect bits and,
            // for a primitive, the constant in second position. When neither
            // changed, only its binding facts can have: no scan of siblings.
            let effects_changed =
                self.nodes[target.index()].flags().0 & effect_bits != effects_before;
            let second_operand = matches!(
                self.view(parent),
                View::Prim { args, .. } if args.get(1) == Some(&target)
            );
            let j_shape = matches!(self.view(parent), View::JBin { .. } | View::JCall { .. });
            if effects_changed || second_operand || j_shape || self.update_facts(parent) || tail_changed {
                self.repair_with_tail_child(parent, tail_changed.then_some(target));
            }
            // Array.isArray recognises a two-edge callee shape, not just purity.
            if matches!(self.view(parent), View::JDot { .. }) {
                if let Some(grandparent) = self.parents[parent.index()] {
                    if matches!(self.view(grandparent), View::JCall { .. }) {
                        self.repair(grandparent);
                    }
                }
            }
        }
        // Moving a subtree up to an ancestor's slot removes boundaries between
        // its uses and their binders and adds none, so `CAPTURED` stays right.
        if !self.bulk && !descendant && !local {
            self.capture_moved(target);
        }
        self.drain_dead();
    }

    /// Detach an attached node so that new content can be built around it
    /// with [`Self::new_node_in`]. Its old parent still names it and must be
    /// released, or replaced, before the tree is read or validated again:
    /// releasing skips children that were detached or adopted elsewhere. The
    /// detached root keeps its use weight, so reattaching it in a slot of the
    /// same weight costs no walk.
    pub fn detach(&mut self, node: NodeId) {
        self.node(node);
        assert!(
            self.parents[node.index()].is_some(),
            "detach needs an attached node"
        );
        if !self.bulk {
            // Pin the weight before the parent link that derives it is cut.
            let weight = self.weight(node);
            self.weights[node.index()] = weight;
        }
        self.parents[node.index()] = None;
    }

    /// The use weight of a slot: 1, doubled for each switch default above it
    /// that today's counts visit twice.
    pub fn weight_of(&mut self, node: NodeId) -> u32 {
        if self.bulk { 1 } else { self.weight(node) }
    }

    /// Stop marking unused pure bindings dead as their last use disappears.
    /// Rounds that must see the tree as today's passes do (a dead binding
    /// still has its size and its place) keep this on.
    pub fn defer_deaths(&mut self) {
        self.deaths_deferred = true;
        self.death_candidates.clear();
    }

    /// Mark every unused pure binding dead, cascading, and resume marking
    /// them as edits remove last uses. One scan of the variable table.
    pub fn resume_deaths(&mut self) {
        self.deaths_deferred = false;
        for var in 0..self.vars.len() {
            if self.vars.uses[var] == 0 {
                if let Some(binder) = self.vars.binder[var] {
                    self.death_candidates.push(binder);
                }
            }
        }
        self.drain_dead();
    }

    /// Release a detached subtree. Attached nodes must be edited with `replace`.
    pub fn release(&mut self, root: NodeId) {
        self.node(root);
        assert!(
            self.parents[root.index()].is_none(),
            "release requires a detached root"
        );
        self.release_nodes(root, None, true);
        self.drain_dead();
    }
    fn release_nodes(&mut self, root: NodeId, keep: Option<NodeId>, free_root: bool) {
        let root_weight = if self.bulk { 1 } else { self.weight(root) };
        let mut stack = std::mem::take(&mut self.release_stack);
        debug_assert!(stack.is_empty());
        stack.push((root, root_weight));
        while let Some((id, weight)) = stack.pop() {
            if Some(id) == keep {
                continue;
            }
            for i in 0..self.view(id).child_count() {
                let child = self.view(id).child_at(i);
                // A child detached from this node, or adopted by another,
                // is no longer part of what is released (`detach`).
                if self.parents[child.index()] != Some(id) {
                    continue;
                }
                stack.push((
                    child,
                    weight
                        .checked_mul(self.edge_weight(id, child))
                        .expect("Bir use weight overflow"),
                ));
            }
            if !self.bulk {
                self.adjust_direct(id, -i64::from(weight));
            }
            self.unbind(id);
            self.register_kind(self.nodes[id.index()], false);
            self.weights[id.index()] = 0;
            if id != root || free_root {
                self.nodes[id.index()] = Node::free();
                self.parents[id.index()] = None;
                if !self.cold.is_empty() {
                    self.cold[id.index()] = None;
                }
                self.free_nodes.push(id);
            }
        }
        self.release_stack = stack;
    }
    fn drain_dead(&mut self) {
        // A worklist avoids recursive cascades when releasing one value kills another.
        while let Some(id) = self.death_candidates.pop() {
            if self.nodes[id.index()].op() == Op::Free {
                continue;
            }
            if let View::Let {
                var,
                value: Some(value),
                ..
            } = self.view(id)
            {
                if self.vars.uses(var) == 0 && self.node(value).flags().contains(NodeFlags::PURE) {
                    self.nodes[id.index()].kill_value();
                    self.vars.fact[var.index()] = Fact::Unknown;
                    self.release_nodes(value, None, true);
                    self.repair(id);
                }
            }
        }
    }

    /// Copy one childless node with its payload words, flags and source
    /// metadata, as a detached root. Constant: no map and no vector, unlike
    /// [`Self::copy_subtree`]. A copied reference gets its own site.
    pub(crate) fn copy_leaf(&mut self, id: NodeId) -> NodeId {
        let node = self.node(id);
        assert!(self.view(id).children().is_empty(), "copy_leaf needs a leaf");
        let new = self.allocate(node);
        self.bind(new);
        if !self.bulk {
            self.adjust_direct(new, 1);
        }
        if let Some(cold) = self.cold(id) {
            self.set_cold(new, cold);
        }
        new
    }

    /// Copy a subtree, freshening every internal binder and static label. Explicit
    /// renaming applies only to free variables; internal binders always win.
    pub fn copy_subtree(&mut self, root: NodeId, renaming: &[(VarId, VarId)]) -> NodeId {
        self.copy_subtree_recording(root, renaming, &mut Vec::new(), &mut Vec::new())
    }

    /// [`Self::copy_subtree`], appending `(fresh, source)` for every binder
    /// it freshens, in allocation order (the bridge names fresh variables in
    /// that order), and `(fresh, source)` for every static label.
    pub fn copy_subtree_recording(
        &mut self,
        root: NodeId,
        renaming: &[(VarId, VarId)],
        fresh_vars: &mut Vec<(VarId, VarId)>,
        fresh_labels: &mut Vec<(u32, u32)>,
    ) -> NodeId {
        self.copy_subtree_with_scratch(root, renaming, fresh_vars, fresh_labels,
            &mut CopyScratch::default())
    }

    /// Copy with caller-owned traversal storage; binder allocation order and
    /// free-variable renaming are identical to `copy_subtree_recording`.
    pub(crate) fn copy_subtree_with_scratch(
        &mut self,
        root: NodeId,
        renaming: &[(VarId, VarId)],
        fresh_vars: &mut Vec<(VarId, VarId)>,
        fresh_labels: &mut Vec<(u32, u32)>,
        scratch: &mut CopyScratch,
    ) -> NodeId {
        // Dense rows are indexed by output handles, including recycled slots.
        // Reserve the already allocated arena domain, not each visited handle.
        scratch.nodes.reserve_domain(self.nodes.capacity());
        let CopyScratch { order, stack, vars, funcs, catches, labels, js, nodes } = scratch;
        order.clear();
        stack.clear();
        vars.clear();
        funcs.clear();
        catches.clear();
        labels.clear();
        js.clear();
        nodes.clear();
        stack.push(root);
        while let Some(id) = stack.pop() {
            order.push(id);
            let view = self.view(id);
            stack.extend((0..view.child_count()).map(|i| view.child_at(i)));
        }
        vars.extend(renaming.iter().copied());
        for &id in order.iter() {
            let run = self.binder_run(id);
            for slot in 0..run.len() {
                let Some(var) = run.at(self, slot) else { continue };
                let fresh = self.new_var_id(self.vars.name(var), index(self.vars.len()));
                self.vars.flags[fresh.index()].0 =
                    self.vars.flags[var.index()].0 & !VarFlags::EXPORTED;
                fresh_vars.push((fresh, var));
                vars.insert(var, fresh);
            }
        }
        for &id in order.iter() {
            match self.view(id) {
                View::Fun { header, .. } | View::JFun { header, .. } => {
                    let old = *self.function(header);
                    let params = if old.flags & FuncHeader::INDIRECT_PARAMS != 0 {
                        let start = index(self.vars.function_params.len());
                        for i in 0..old.params.len() {
                            let original = self.function_parameter(header, i);
                            self.vars.function_params.push(vars[&original]);
                        }
                        VarSpan { start, len: old.params.len }
                    } else {
                        VarSpan {
                            start: old.params.iter().next().map_or(0, |v| vars[&v].0),
                            len: old.params.len,
                        }
                    };
                    // Attributes are immutable cold metadata. Only the header
                    // and its owner/parameters need fresh identities.
                    let new = FuncId(index(self.vars.funcs.len()));
                    self.func_owners.push(None);
                    self.vars.funcs.push(FuncHeader { params, ..old });
                    if self.js_scope.is_some() {
                        // The copy's parameters are bound where the copy is
                        // made, as its other binders are (`bind`): no scope
                        // closes over a copy, so the open scope reads the
                        // copy's sites as its own.
                        let params: SmallVec<[VarId; 4]> =
                            (0..old.params.len()).map(|i| self.function_parameter(new, i)).collect();
                        if let Some(scope) = &mut self.js_scope {
                            scope.names.copied(header, new);
                            for var in params {
                                scope.names.bind(var);
                            }
                        }
                    }
                    funcs.insert(header, new);
                }
                View::Catch { header, .. } => {
                    let old = *self.catch(header);
                    let label =
                        u32::try_from(self.pools.next_label).expect("static label overflow");
                    let params = VarSpan {
                        start: old.params.iter().next().map_or(0, |v| vars[&v].0),
                        len: old.params.len,
                    };
                    let new = self.catch_header(label, params);
                    catches.insert(header, new);
                    fresh_labels.push((label, old.label));
                    labels.insert(old.label, label);
                }
                _ => {}
            }
        }
        for &id in order.iter() {
            if let View::JRecordRest { info, .. } | View::SRest { info, .. } = self.view(id) {
                if let JsPayload::Rest(fields) = self.javascript(info) {
                    let fields = *fields;
                    let start = index(self.pools.rest_fields.len());
                    for i in 0..fields.len {
                        let field = self.pools.rest_fields[(fields.start + i) as usize];
                        self.pools.rest_fields.push(RestField {
                            name: field.name,
                            binding: field.binding.map(|v| vars.get(&v).copied().unwrap_or(v)),
                        });
                    }
                    let copied = self.js_info(JsPayload::Rest(RestSpan { start, len: fields.len }));
                    js.insert(info, copied);
                }
            }
        }
        for &id in order.iter().rev() {
            let packed = self.node(id).remap(
                &mut self.lists,
                &super::node::Renaming {
                    nodes,
                    vars,
                    funcs,
                    catches,
                    labels,
                    js,
                },
            );
            let new = self.allocate(packed);
            self.bind(new);
            for i in 0..self.view(new).child_count() {
                let child = self.view(new).child_at(i);
                self.parents[child.index()] = Some(new);
                let multiplier = self.edge_weight(new, child);
                if !self.bulk && multiplier != 1 {
                    self.adjust_counts(child, i64::from(multiplier) - 1);
                }
            }
            if !self.bulk { self.adjust_direct(new, 1); }
            self.repair(new);
            if let Some(cold) = self.cold(id) {
                self.set_cold(new, cold);
            }
            nodes.insert(id, new);
        }
        let result = nodes[&root];
        self.capture_moved(result);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::{LamLoc, SwitchDispatch};
    use crate::name::Name;

    fn lit(b: &mut Bir) -> NodeId {
        let value = b.intern_const(Constant::Int(7));
        b.new_node(View::Const { value }, 0)
    }
    fn var(b: &mut Bir, v: VarId) -> NodeId {
        b.new_node(View::Var { var: v }, 0)
    }
    fn valid(b: &Bir, root: NodeId) {
        b.validate(Some(root))
            .unwrap_or_else(|e| panic!("{e}\n{}", b.dump()));
    }

    #[test]
    fn retained_copy_scratch_reuses_buffers_and_clears_renames() {
        let mut b = Bir::default();
        let free = b.new_var_id(Name::new("free"), 0);
        let renamed = b.new_var_id(Name::new("renamed"), 1);
        let root = b.new_node(View::Var { var: free }, 0);
        let mut scratch = CopyScratch::default();
        let mut vars = Vec::new();
        let mut labels = Vec::new();
        let copied = b.copy_subtree_with_scratch(root, &[(free, renamed)],
            &mut vars, &mut labels, &mut scratch);
        assert!(matches!(b.view(copied), View::Var { var } if var == renamed));
        b.release(copied);
        let capacities = |s: &CopyScratch| [s.order.capacity(), s.stack.capacity(),
            s.vars.capacity(), s.funcs.capacity(), s.catches.capacity(),
            s.labels.capacity(), s.js.capacity(), s.nodes.capacity()];
        let before = capacities(&scratch);
        let measured = allocation_counter::measure(|| {
            for _ in 0..10_000 {
                let copied = b.copy_subtree_with_scratch(root, &[],
                    &mut vars, &mut labels, &mut scratch);
                assert!(matches!(b.view(copied), View::Var { var } if var == free));
                b.release(copied);
            }
        });
        assert_eq!(measured.count_total, 0, "{measured:?}");
        assert_eq!(capacities(&scratch), before);
        assert_eq!(b.vars.uses(free), 1);
        assert_eq!(b.vars.uses(renamed), 0);
        b.validate(Some(root)).unwrap();
    }

    #[test]
    fn wide_rest_copy_uses_flat_fields_without_allocations() {
        let mut b = Bir::default();
        let name = b.intern_text("excluded");
        let info = b.rest_info(std::iter::repeat_n(RestField { name, binding: None }, 10_000));
        let value = b.new_node(View::JNull, 0);
        let root = b.new_node(View::JRecordRest { value, info }, 0);
        let mut scratch = CopyScratch::default();
        let mut vars = Vec::new();
        let mut labels = Vec::new();
        let copy = b.copy_subtree_with_scratch(root, &[], &mut vars, &mut labels, &mut scratch);
        b.release(copy);
        b.pools.rest_fields.reserve(10_000);
        b.pools.js.reserve(1);
        let before = [b.pools.rest_fields.capacity(), b.pools.js.capacity(),
            b.nodes.capacity(), b.parents.capacity(), b.free_nodes.capacity(),
            scratch.order.capacity(), scratch.stack.capacity(), scratch.nodes.capacity(),
            scratch.js.capacity()];
        let measured = allocation_counter::measure(|| {
            let copy = b.copy_subtree_with_scratch(root, &[], &mut vars, &mut labels, &mut scratch);
            let View::JRecordRest { info, .. } = b.view(copy) else { panic!() };
            let JsPayload::Rest(fields) = b.javascript(info) else { panic!() };
            assert_eq!(b.rest_fields(*fields).len(), 10_000);
            b.release(copy);
        });
        assert_eq!(measured.count_total, 0, "{measured:?}");
        assert_eq!([b.pools.rest_fields.capacity(), b.pools.js.capacity(),
            b.nodes.capacity(), b.parents.capacity(), b.free_nodes.capacity(),
            scratch.order.capacity(), scratch.stack.capacity(), scratch.nodes.capacity(),
            scratch.js.capacity()], before);
        assert_eq!(std::mem::size_of::<RestSpan>(), 8);
        b.validate(Some(root)).unwrap();
    }

    #[test]
    fn layout() {
        use std::mem::size_of;
        assert_eq!(size_of::<Node>(), 16);
        assert_eq!(size_of::<Op>(), 1);
        assert_eq!(size_of::<NodeFlags>(), 1);
        assert_eq!(size_of::<Fact>(), 8);
        assert_eq!(size_of::<VarFlags>(), 1);
        assert_eq!(size_of::<VarSpan>(), 8);
        assert_eq!(size_of::<FuncHeader>(), 20);
        assert_eq!(size_of::<CatchHeader>(), 16);
        assert_eq!(size_of::<NodeId>(), 4);
        assert_eq!(size_of::<ListId>(), 4);
        assert_eq!(size_of::<VarId>(), 4);
        assert_eq!(size_of::<ConstId>(), 4);
        assert_eq!(size_of::<PrimId>(), 4);
        assert_eq!(size_of::<FuncId>(), 4);
        assert_eq!(size_of::<SwitchId>(), 4);
        assert_eq!(size_of::<ColdId>(), 4);
        assert_eq!(size_of::<StrId>(), 4);
    }

    fn has_exit_flag(b: &Bir, id: NodeId) -> bool {
        b.node(id).flags().contains(NodeFlags::HAS_EXIT)
    }

    fn switched_jump(b: &mut Bir, continue_: bool) -> (NodeId, NodeId) {
        let jump = b.new_node(if continue_ { View::Continue } else { View::Break }, 0);
        let scrutinee = lit(b);
        let header = b.switch_header(SwitchInput {
            keys: vec![], clauses: vec![], constants: 0, consts_full: false,
            blocks_full: false, has_default: true, dispatch: SwitchDispatch::Direct,
        });
        (b.new_node(View::Switch { scrutinee, actions: &[jump], header }, 0), jump)
    }

    #[test]
    fn loop_label_facts_follow_boundaries_edits_and_validation() {
        assert_eq!(std::mem::size_of::<super::super::tail_facts::LoopFacts>(), 1);
        for continue_ in [false, true] {
            let mut b = Bir::default();
            let (body, jump) = switched_jump(&mut b, continue_);
            let condition = lit(&mut b);
            let inner = b.new_node(View::While { condition, body }, 0);
            let condition = lit(&mut b);
            let outer = b.new_node(View::While { condition, body: inner }, 0);
            assert!(b.loop_needs_label(inner));
            assert!(!b.loop_needs_label(outer));
            valid(&b, outer);
            let replacement = lit(&mut b);
            b.replace(jump, replacement);
            assert!(!b.loop_needs_label(inner));
            valid(&b, outer);
            let replacement = b.new_node(View::Break, 0);
            b.replace(jump, replacement);
            assert!(b.loop_needs_label(inner));
            valid(&b, outer);
            b.loop_facts[inner.index()].0 = 0;
            assert_eq!(b.validate(Some(outer)), Err("stale loop-label fact".to_string()));

            let mut b = Bir::default();
            let body = b.new_node(if continue_ { View::Continue } else { View::Break }, 0);
            let condition = lit(&mut b);
            let root = b.new_node(View::While { condition, body }, 0);
            assert!(!b.loop_needs_label(root));
            valid(&b, root);

            let mut b = Bir::default();
            let (body, _) = switched_jump(&mut b, continue_);
            let params = b.new_vars(&[]);
            let header = b.function_header(params, FunctionAttribute::default(), LamLoc::NONE);
            let body = b.new_node(View::Fun { body, header }, 0);
            let condition = lit(&mut b);
            let root = b.new_node(View::While { condition, body }, 0);
            assert!(!b.loop_needs_label(root));
            valid(&b, root);
        }
    }

    #[test]
    fn loop_label_facts_ten_thousand_nested_loops() {
        let mut b = Bir::default();
        let (mut root, _) = switched_jump(&mut b, false);
        let mut inner = root;
        for i in 0..10_000 {
            let condition = lit(&mut b);
            root = b.new_node(View::While { condition, body: root }, 0);
            if i == 0 { inner = root; }
        }
        assert_eq!(b.loop_fact_folds.get(), 10_000);
        println!("10,000 nested loops: {} construction folds", b.loop_fact_folds.get());
        assert!(b.loop_needs_label(inner));
        assert!(!b.loop_needs_label(root));
        valid(&b, root);
        assert_eq!(b.loop_fact_folds.get(), 20_000);
    }

    #[test]
    fn has_exit_is_recorded_when_a_node_is_built_and_stops_at_a_function() {
        let mut b = Bir::default();
        let header = b.catch_header(1, VarSpan::default());
        let exit = b.new_node(View::Exit { label: 1, args: &[] }, 0);
        let other = lit(&mut b);
        let seq = b.new_node(View::Seq { first: other, second: exit }, 0);
        let condition = lit(&mut b);
        let else_ = lit(&mut b);
        let branch = b.new_node(View::If { condition, then_: seq, else_ }, 0);
        // An exit under a function does not leave it (lam_exit_code.ml:28).
        let params = b.new_vars(&[]);
        let function = b.function_header(params, FunctionAttribute::default(), LamLoc::NONE);
        let closed = b.new_node(View::Exit { label: 1, args: &[] }, 0);
        let fun = b.new_node(View::Fun { body: closed, header: function }, 0);
        let body = b.new_node(View::Seq { first: fun, second: branch }, 0);
        let handler = lit(&mut b);
        let root = b.new_node(View::Catch { body, handler, header }, 0);
        for flagged in [exit, seq, branch, closed, body, root] {
            assert!(has_exit_flag(&b, flagged));
            assert!(b.node(flagged).flags().contains(NodeFlags::HAS_STATEMENT));
        }
        for clear in [other, condition, else_, fun, handler] {
            assert!(!has_exit_flag(&b, clear));
            assert!(!b.node(clear).flags().contains(NodeFlags::HAS_STATEMENT));
        }
        valid(&b, root);
    }

    #[test]
    fn has_statement_marks_statement_forms_without_exits() {
        let mut b = Bir::default();
        let v = b.new_var_id(Name::new("x"), 0);
        let value = lit(&mut b);
        let assign = b.new_node(View::Assign { var: v, value }, 0);
        let first = lit(&mut b);
        let seq = b.new_node(View::Seq { first, second: assign }, 0);
        let condition = b.new_node(View::Break, 0);
        let body = lit(&mut b);
        let looped = b.new_node(View::While { condition, body }, 0);
        let root = b.new_node(View::Seq { first: seq, second: looped }, 0);
        for flagged in [assign, seq, condition, looped, root] {
            assert!(b.node(flagged).flags().contains(NodeFlags::HAS_STATEMENT));
            assert!(!has_exit_flag(&b, flagged));
        }
        for clear in [value, first, body] {
            assert!(!b.node(clear).flags().contains(NodeFlags::HAS_STATEMENT));
        }
        valid(&b, root);
        let mut flags = b.node(first).flags();
        flags.0 |= NodeFlags::HAS_STATEMENT;
        b.nodes[first.index()].set_flags(flags);
        assert_eq!(b.validate(Some(root)), Err("stale statement-form flag".to_string()));
    }

    #[test]
    fn has_exit_follows_an_edit_up_ten_thousand_parents() {
        let mut b = Bir::default();
        b.catch_header(1, VarSpan::default());
        let exit = b.new_node(View::Exit { label: 1, args: &[] }, 0);
        let mut root = exit;
        for _ in 0..10_000 {
            let first = lit(&mut b);
            root = b.new_node(View::Seq { first, second: root }, 0);
        }
        assert!(has_exit_flag(&b, root));
        valid(&b, root);
        let replacement = lit(&mut b);
        b.replace(exit, replacement);
        assert!(!has_exit_flag(&b, root));
        valid(&b, root);
        let again = b.new_node(View::Exit { label: 1, args: &[] }, 0);
        b.replace(exit, again);
        assert!(has_exit_flag(&b, root));
        valid(&b, root);
    }

    #[test]
    fn validate_rejects_a_stale_exit_flag() {
        let mut b = Bir::default();
        b.catch_header(1, VarSpan::default());
        let exit = b.new_node(View::Exit { label: 1, args: &[] }, 0);
        let first = lit(&mut b);
        let root = b.new_node(View::Seq { first, second: exit }, 0);
        valid(&b, root);
        for (node, set) in [(root, false), (first, true)] {
            let old = b.node(node).flags();
            let mut flags = old;
            if set {
                flags.0 |= NodeFlags::HAS_EXIT;
            } else {
                flags.0 &= !NodeFlags::HAS_EXIT;
            }
            b.nodes[node.index()].set_flags(flags);
            assert_eq!(b.validate(Some(root)), Err("stale exit flag".to_string()));
            b.nodes[node.index()].set_flags(old);
        }
        valid(&b, root);
    }

    #[test]
    fn replace_release_and_reuse() {
        let mut b = Bir::default();
        let v = b.new_var_id(Name::new("x"), 0);
        let value = lit(&mut b);
        let body = var(&mut b, v);
        let root = b.new_node(
            View::Let {
                var: v,
                value: Some(value),
                body,
            },
            0,
        );
        valid(&b, root);
        let replacement = lit(&mut b);
        b.replace(body, replacement);
        assert_eq!(b.vars.uses(v), 0);
        assert!(b.node(root).flags().contains(NodeFlags::DEAD));
        assert_eq!(b.vars.fact(v), Fact::Unknown);
        valid(&b, root);
        b.replace(root, body);
        valid(&b, root);
        b.release(root);
        b.validate(None).unwrap();
        let reused = lit(&mut b);
        assert_eq!(root, reused);
        valid(&b, reused);
    }

    #[test]
    fn default_weights_copy_and_capture() {
        let mut b = Bir::default();
        let v = b.new_var_id(Name::new("free"), 0);
        let condition = lit(&mut b);
        let use_ = var(&mut b, v);
        let h = b.switch_header(SwitchInput {
            keys: vec![],
            clauses: vec![],
            constants: 0,
            consts_full: false,
            blocks_full: false,
            has_default: true,
            dispatch: SwitchDispatch::Direct,
        });
        let switch = b.new_node(
            View::Switch {
                scrutinee: condition,
                actions: &[use_],
                header: h,
            },
            0,
        );
        assert_eq!(b.vars.uses(v), 2);
        valid(&b, switch);
        let params = b.new_vars(&[Name::new("p")]);
        let parameter = params.iter().next().unwrap();
        let p = var(&mut b, parameter);
        let body = b.new_node(
            View::Seq {
                first: switch,
                second: p,
            },
            0,
        );
        let h = b.function_header(params, FunctionAttribute::default(), LamLoc::NONE);
        let fun = b.new_node(View::Fun { body, header: h }, 1);
        valid(&b, fun);
        assert!(b.vars.flags(v).contains(VarFlags::CAPTURED));
        assert!(!b.vars.flags(parameter).contains(VarFlags::CAPTURED));
        let copy = b.copy_subtree(fun, &[]);
        let root = b.new_node(
            View::Seq {
                first: fun,
                second: copy,
            },
            0,
        );
        valid(&b, root);
        assert_eq!(b.vars.uses(v), 4);
        let View::Fun {
            header: copied_h, ..
        } = b.view(copy)
        else {
            panic!()
        };
        assert_ne!(b.function(copied_h).params, params);
        b.release(root);
        b.validate(None).unwrap();
    }

    #[test]
    fn effects_and_facts_follow_nested_edits() {
        let mut b = Bir::default();
        let v = b.new_var_id(Name::new("f"), 0);
        let value = lit(&mut b);
        let body = var(&mut b, v);
        let root = b.new_node(
            View::Let {
                var: v,
                value: Some(value),
                body,
            },
            0,
        );
        assert!(matches!(b.vars.fact(v), Fact::Const(_)));
        let text = b.intern_text("sideEffect()");
        let raw = b.new_node(View::JRaw { text }, 0);
        b.replace(value, raw);
        assert_eq!(b.vars.fact(v), Fact::Unknown);
        assert!(!b.node(root).flags().contains(NodeFlags::PURE));
        valid(&b, root);
        let new = lit(&mut b);
        b.replace(body, new);
        assert!(!b.node(root).flags().contains(NodeFlags::DEAD));
        valid(&b, root);
    }

    #[test]
    fn cascading_dead_bindings() {
        let mut b = Bir::default();
        let x = b.new_var_id(Name::new("x"), 0);
        let y = b.new_var_id(Name::new("y"), 1);
        let xv = lit(&mut b);
        let yv = var(&mut b, x);
        let body = var(&mut b, y);
        let inner = b.new_node(
            View::Let {
                var: y,
                value: Some(yv),
                body,
            },
            0,
        );
        let root = b.new_node(
            View::Let {
                var: x,
                value: Some(xv),
                body: inner,
            },
            0,
        );
        valid(&b, root);
        let replacement = lit(&mut b);
        b.replace(body, replacement);
        assert!(b.node(root).flags().contains(NodeFlags::DEAD));
        assert!(b.node(inner).flags().contains(NodeFlags::DEAD));
        valid(&b, root);
    }

    #[test]
    fn metadata_and_deterministic_dump() {
        let mut b = Bir::default();
        let value = b.intern_const(Constant::Int(1));
        assert_eq!(value, b.intern_const(Constant::Int(1)));
        let s = b.intern_text("hello\nλ");
        assert_eq!(s, b.intern_text("hello\nλ"));
        assert_eq!(b.text(s), "hello\nλ");
        let root = b.new_node(View::Const { value }, 0);
        assert!(b.cold.is_empty());
        b.set_cold(
            root,
            Cold {
                loc: LamLoc::NONE,
                comment: Some(s),
            },
        );
        let copied = b.copy_subtree(root, &[]);
        assert_eq!(b.cold(copied).unwrap().comment, Some(s));
        let tree = b.new_node(
            View::Seq {
                first: root,
                second: copied,
            },
            0,
        );
        valid(&b, tree);
        assert_eq!(b.dump(), b.dump());
        assert!(b.dump().contains("const0 Int(1)"));
    }

    #[test]
    fn validator_rejects_corruption() {
        let mut b = Bir::default();
        let v = b.new_var_id(Name::new("v"), 0);
        let root = var(&mut b, v);
        b.vars.uses[v.index()] += 1;
        assert!(
            b.validate(Some(root))
                .unwrap_err()
                .contains("use count")
        );
        b.vars.uses[v.index()] -= 1;
        valid(&b, root);
        let other = lit(&mut b);
        assert!(
            b.validate(Some(root))
                .unwrap_err()
                .contains("unreachable")
        );
        b.release(other);
        valid(&b, root);
    }

    #[test]
    fn seeded_random_edits_validate_after_every_edit() {
        fn with_weighted_default(b: &mut Bir, body: NodeId) -> NodeId {
            let scrutinee = lit(b);
            let header = b.switch_header(SwitchInput {
                keys: vec![],
                clauses: vec![],
                constants: 0,
                consts_full: false,
                blocks_full: false,
                has_default: true,
                dispatch: SwitchDispatch::Direct,
            });
            b.new_node(
                View::Switch {
                    scrutinee,
                    actions: &[body],
                    header,
                },
                0,
            )
        }
        // xorshift64: fixed seed and no dependency on a platform RNG or hash order.
        let mut state = 0x7b8c_9d01_2345_6789u64;
        let mut rand = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let mut b = Bir::for_typed_exprs(64);
        let vars: Vec<_> = (0..8).map(|i| b.new_var_id(Name::new("free"), i)).collect();
        let initial = var(&mut b, vars[0]);
        let mut root = with_weighted_default(&mut b, initial);
        b.validate(Some(root)).unwrap();
        for step in 0..5000 {
            // Start every edit in a weighted module with all cache entries warm,
            // so the oracle also detects missing local invalidation.
            assert!(b.weighted_switches > 0);
            let mut pending = vec![root];
            while let Some(id) = pending.pop() {
                b.weight(id);
                pending.extend(b.view(id).children());
            }
            match rand() % 9 {
                0 => {
                    let new = var(&mut b, vars[(rand() % 8) as usize]);
                    b.replace(root, new);
                }
                1 => {
                    let new = lit(&mut b);
                    root = b.new_node(
                        View::Seq {
                            first: root,
                            second: new,
                        },
                        0,
                    );
                }
                2 => {
                    let copy = b.copy_subtree(root, &[]);
                    b.replace(root, copy);
                }
                3 => {
                    let params = b.new_vars(&[Name::new("p")]);
                    let header =
                        b.function_header(params, FunctionAttribute::default(), LamLoc::NONE);
                    root = b.new_node(View::Fun { body: root, header }, 1);
                }
                4 => {
                    let var = b.new_var_id(Name::new("binding"), index(b.vars.len()));
                    let value = lit(&mut b);
                    root = b.new_node(
                        View::Let {
                            var,
                            value: Some(value),
                            body: root,
                        },
                        0,
                    );
                }
                5 => {
                    let children = b.view(root).children();
                    if let Some(&child) = children.last() {
                        b.replace(root, child);
                    }
                }
                6 => {
                    let scrutinee = lit(&mut b);
                    let header = b.switch_header(SwitchInput {
                        keys: vec![],
                        clauses: vec![],
                        constants: 0,
                        consts_full: false,
                        blocks_full: false,
                        has_default: true,
                        dispatch: SwitchDispatch::Direct,
                    });
                    root = b.new_node(
                        View::Switch {
                            scrutinee,
                            actions: &[root],
                            header,
                        },
                        0,
                    );
                }
                7 => {
                    let live: Vec<_> = b
                        .nodes
                        .iter()
                        .enumerate()
                        .filter(|(_, n)| n.op() != Op::Free)
                        .map(|(i, _)| NodeId(index(i)))
                        .collect();
                    let target = live[(rand() as usize) % live.len()];
                    let replacement = lit(&mut b);
                    b.replace(target, replacement);
                }
                _ => {
                    b.release(root);
                    b.validate(None).unwrap();
                    root = lit(&mut b);
                }
            }
            if b.weighted_switches == 0 {
                root = with_weighted_default(&mut b, root);
            }
            b.validate(Some(root))
                .unwrap_or_else(|e| panic!("step {step}: {e}\n{}", b.dump()));
        }
    }
}

#[cfg(test)]
mod constructor_tests {
    use super::*;
    use crate::lambda::{ApplyStatus, SwitchDispatch};
    use crate::name::Name;
    fn leaf(b: &mut Bir) -> NodeId {
        b.new_node(View::JNull, 0)
    }

    macro_rules! case {
        ($name:ident, |$b:ident| $build:block, $op:ident) => {
            #[test]
            fn $name() {
                let mut $b = Bir::default();
                let root = $build;
                assert_eq!($b.node(root).op(), Op::$op);
                $b.validate(Some(root)).unwrap();
                let copied = $b.copy_subtree(root, &[]);
                let pair = $b.new_node(
                    View::Seq {
                        first: root,
                        second: copied,
                    },
                    0,
                );
                $b.validate(Some(pair)).unwrap();
                $b.replace(pair, copied);
                $b.validate(Some(pair)).unwrap();
                $b.release(pair);
                $b.validate(None).unwrap();
            }
        };
    }
    case!(
        constructs_var,
        |b| {
            let var = b.new_var_id(Name::new("v"), 0);
            b.new_node(View::Var { var }, 0)
        },
        Var
    );
    case!(
        constructs_global,
        |b| {
            let path = b.intern_text("module");
            let module = b.import(Import {
                name: Name::new("Module"),
                path,
            });
            b.new_node(View::Global { module }, 0)
        },
        Global
    );
    case!(
        constructs_const,
        |b| {
            let value = b.intern_const(Constant::Int(1));
            b.new_node(View::Const { value }, 0)
        },
        Const
    );
    case!(
        constructs_apply,
        |b| {
            let callee = leaf(&mut b);
            let args = [leaf(&mut b), leaf(&mut b)];
            let info = b.apply_info(crate::lambda::ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Na,
            });
            b.new_node(
                View::Apply {
                    callee,
                    args: &args,
                    info,
                },
                0,
            )
        },
        Apply
    );
    case!(
        constructs_fun,
        |b| {
            let body = leaf(&mut b);
            let params = b.new_vars(&[Name::new("p")]);
            let header = b.function_header(params, FunctionAttribute::default(), LamLoc::NONE);
            b.new_node(View::Fun { body, header }, 0)
        },
        Fun
    );
    case!(
        constructs_let,
        |b| {
            let var = b.new_var_id(Name::new("v"), 0);
            let value = Some(leaf(&mut b));
            let body = leaf(&mut b);
            b.new_node(View::Let { var, value, body }, 0)
        },
        Let
    );
    case!(
        constructs_letrec,
        |b| {
            let first = b
                .new_vars(&[Name::new("a"), Name::new("b")])
                .iter()
                .next()
                .unwrap();
            let values = [leaf(&mut b), leaf(&mut b)];
            let body = leaf(&mut b);
            b.new_node(
                View::LetRec {
                    first,
                    values: &values,
                    body,
                },
                0,
            )
        },
        LetRec
    );
    case!(
        constructs_prim,
        |b| {
            let args = [leaf(&mut b), leaf(&mut b)];
            let primitive = b.intern_prim(PrimPayload {
                primitive: Primitive::Paddint,
                loc: LamLoc::NONE,
            });
            b.new_node(
                View::Prim {
                    args: &args,
                    primitive,
                },
                0,
            )
        },
        Prim
    );
    case!(
        constructs_switch,
        |b| {
            let scrutinee = leaf(&mut b);
            let actions = [leaf(&mut b)];
            let header = b.switch_header(SwitchInput {
                keys: vec![],
                clauses: vec![],
                constants: 0,
                consts_full: false,
                blocks_full: false,
                has_default: true,
                dispatch: SwitchDispatch::Direct,
            });
            b.new_node(
                View::Switch {
                    scrutinee,
                    actions: &actions,
                    header,
                },
                0,
            )
        },
        Switch
    );
    case!(
        constructs_strswitch,
        |b| {
            let scrutinee = leaf(&mut b);
            let actions = [leaf(&mut b)];
            let header = b.switch_header(SwitchInput {
                keys: vec![],
                clauses: vec![],
                constants: 0,
                consts_full: false,
                blocks_full: false,
                has_default: true,
                dispatch: SwitchDispatch::Direct,
            });
            b.new_node(
                View::StrSwitch {
                    scrutinee,
                    actions: &actions,
                    header,
                },
                0,
            )
        },
        StrSwitch
    );
    case!(
        constructs_exit,
        |b| {
            b.catch_header(1, VarSpan::default());
            let label = 1;
            let args = [leaf(&mut b), leaf(&mut b)];
            b.new_node(View::Exit { label, args: &args }, 0)
        },
        Exit
    );
    case!(
        constructs_catch,
        |b| {
            let body = leaf(&mut b);
            let handler = leaf(&mut b);
            let params = b.new_vars(&[Name::new("p")]);
            let header = b.catch_header(1, params);
            b.new_node(
                View::Catch {
                    body,
                    handler,
                    header,
                },
                0,
            )
        },
        Catch
    );
    case!(
        constructs_try,
        |b| {
            let body = leaf(&mut b);
            let exception = b.new_var_id(Name::new("v"), 0);
            let handler = leaf(&mut b);
            b.new_node(
                View::Try {
                    body,
                    exception,
                    handler,
                },
                0,
            )
        },
        Try
    );
    case!(
        constructs_tryfinally,
        |b| {
            let body = leaf(&mut b);
            let finaliser = leaf(&mut b);
            b.new_node(View::TryFinally { body, finaliser }, 0)
        },
        TryFinally
    );
    case!(
        constructs_if,
        |b| {
            let condition = leaf(&mut b);
            let then_ = leaf(&mut b);
            let else_ = leaf(&mut b);
            b.new_node(
                View::If {
                    condition,
                    then_,
                    else_,
                },
                0,
            )
        },
        If
    );
    case!(
        constructs_seq,
        |b| {
            let first = leaf(&mut b);
            let second = leaf(&mut b);
            b.new_node(View::Seq { first, second }, 0)
        },
        Seq
    );
    case!(
        constructs_while,
        |b| {
            let condition = leaf(&mut b);
            let body = leaf(&mut b);
            b.new_node(View::While { condition, body }, 0)
        },
        While
    );
    case!(
        constructs_for,
        |b| {
            let var = b.new_var_id(Name::new("v"), 0);
            let parts = [leaf(&mut b), leaf(&mut b), leaf(&mut b)];
            b.new_node(View::For { var, parts: &parts }, 0)
        },
        For
    );
    case!(
        constructs_forof,
        |b| {
            let var = b.new_var_id(Name::new("v"), 0);
            let iterable = leaf(&mut b);
            let body = leaf(&mut b);
            b.new_node(
                View::ForOf {
                    var,
                    iterable,
                    body,
                },
                0,
            )
        },
        ForOf
    );
    case!(
        constructs_forawaitof,
        |b| {
            let var = b.new_var_id(Name::new("v"), 0);
            let iterable = leaf(&mut b);
            let body = leaf(&mut b);
            b.new_node(
                View::ForAwaitOf {
                    var,
                    iterable,
                    body,
                },
                0,
            )
        },
        ForAwaitOf
    );
    case!(
        constructs_assign,
        |b| {
            let var = b.new_var_id(Name::new("v"), 0);
            let value = leaf(&mut b);
            b.new_node(View::Assign { var, value }, 0)
        },
        Assign
    );
    case!(constructs_break, |b| { b.new_node(View::Break, 0) }, Break);
    case!(
        constructs_continue,
        |b| { b.new_node(View::Continue, 0) },
        Continue
    );
    case!(
        constructs_jbin,
        |b| {
            let left = leaf(&mut b);
            let right = leaf(&mut b);
            b.new_node(View::JBin { left, right }, 0)
        },
        JBin
    );
    case!(
        constructs_jnot,
        |b| {
            let value = leaf(&mut b);
            b.new_node(View::JNot { value }, 0)
        },
        JNot
    );
    case!(
        constructs_jbnot,
        |b| {
            let value = leaf(&mut b);
            b.new_node(View::JBnot { value }, 0)
        },
        JBnot
    );
    case!(
        constructs_jtypeof,
        |b| {
            let value = leaf(&mut b);
            b.new_node(View::JTypeof { value }, 0)
        },
        JTypeof
    );
    case!(
        constructs_jin,
        |b| {
            let left = leaf(&mut b);
            let right = leaf(&mut b);
            b.new_node(View::JIn { left, right }, 0)
        },
        JIn
    );
    case!(
        constructs_jcond,
        |b| {
            let condition = leaf(&mut b);
            let then_ = leaf(&mut b);
            let else_ = leaf(&mut b);
            b.new_node(
                View::JCond {
                    condition,
                    then_,
                    else_,
                },
                0,
            )
        },
        JCond
    );
    case!(
        constructs_jseq,
        |b| {
            let first = leaf(&mut b);
            let second = leaf(&mut b);
            b.new_node(View::JSeq { first, second }, 0)
        },
        JSeq
    );
    case!(
        constructs_jcall,
        |b| {
            let callee = leaf(&mut b);
            let args = [leaf(&mut b), leaf(&mut b)];
            let info = b.js_info(JsPayload::Call(crate::js_ir::CallInfo::default()));
            b.new_node(
                View::JCall {
                    callee,
                    args: &args,
                    info,
                },
                0,
            )
        },
        JCall
    );
    case!(
        constructs_jflatcall,
        |b| {
            let callee = leaf(&mut b);
            let args = leaf(&mut b);
            b.new_node(View::JFlatCall { callee, args }, 0)
        },
        JFlatCall
    );
    case!(
        constructs_jnew,
        |b| {
            let callee = leaf(&mut b);
            let args = [leaf(&mut b), leaf(&mut b)];
            b.new_node(
                View::JNew {
                    callee,
                    args: &args,
                },
                0,
            )
        },
        JNew
    );
    case!(
        constructs_jindex,
        |b| {
            let object = leaf(&mut b);
            let index = leaf(&mut b);
            b.new_node(View::JIndex { object, index }, 0)
        },
        JIndex
    );
    case!(
        constructs_jdot,
        |b| {
            let object = leaf(&mut b);
            let property = b.intern_text("text");
            b.new_node(
                View::JDot {
                    object,
                    property,
                    position: crate::js_ir::arena::FieldPos::NONE,
                },
                0,
            )
        },
        JDot
    );
    case!(
        constructs_jlength,
        |b| {
            let value = leaf(&mut b);
            b.new_node(View::JLength { value }, 0)
        },
        JLength
    );
    case!(
        constructs_jisnullish,
        |b| {
            let value = leaf(&mut b);
            b.new_node(View::JIsNullish { value }, 0)
        },
        JIsNullish
    );
    case!(
        constructs_jstrappend,
        |b| {
            let left = leaf(&mut b);
            let right = leaf(&mut b);
            b.new_node(View::JStrAppend { left, right }, 0)
        },
        JStrAppend
    );
    case!(
        constructs_jfun,
        |b| {
            let body = leaf(&mut b);
            let params = b.new_vars(&[Name::new("p")]);
            let header = b.function_header(params, FunctionAttribute::default(), LamLoc::NONE);
            b.new_node(View::JFun { body, header }, 0)
        },
        JFun
    );
    case!(
        constructs_jobject,
        |b| {
            let values = [leaf(&mut b), leaf(&mut b)];
            let key = b.intern_text("key");
            let info = b.object_info(&[PropertyKey::Literal(key); 2]);
            b.new_node(
                View::JObject {
                    values: &values,
                    info,
                },
                0,
            )
        },
        JObject
    );
    case!(
        constructs_jarray,
        |b| {
            let values = [leaf(&mut b), leaf(&mut b)];
            b.new_node(View::JArray { values: &values }, 0)
        },
        JArray
    );
    case!(
        constructs_jblocklit,
        |b| {
            let values = [leaf(&mut b), leaf(&mut b)];
            let info = b.js_info(JsPayload::Block(
                crate::lambda::lam_tag_info::TagInfo::Tuple,
            ));
            b.new_node(
                View::JBlockLit {
                    values: &values,
                    info,
                },
                0,
            )
        },
        JBlockLit
    );
    case!(
        constructs_joptional,
        |b| {
            let value = leaf(&mut b);
            b.new_node(View::JOptional { value }, 0)
        },
        JOptional
    );
    case!(
        constructs_jjsx,
        |b| {
            let values = [leaf(&mut b), leaf(&mut b)];
            let info = b.js_info(JsPayload::Jsx(JsxHeader::default()));
            b.new_node(
                View::JJsx {
                    values: &values,
                    info,
                },
                0,
            )
        },
        JJsx
    );
    case!(
        constructs_jtemplate,
        |b| {
            let values = [leaf(&mut b), leaf(&mut b)];
            let text = b.intern_text("");
            let info = b.template_info(&[
                TemplatePart {
                    raw: text,
                    cooked: Some(text)
                };
                3
            ], false);
            b.new_node(
                View::JTemplate {
                    values: &values,
                    info,
                },
                0,
            )
        },
        JTemplate
    );
    case!(
        constructs_jtagged,
        |b| {
            let tag = leaf(&mut b);
            let values = [leaf(&mut b), leaf(&mut b)];
            let text = b.intern_text("");
            let info = b.template_info(&[
                TemplatePart {
                    raw: text,
                    cooked: Some(text)
                };
                3
            ], true);
            b.new_node(
                View::JTagged {
                    tag,
                    values: &values,
                    info,
                },
                0,
            )
        },
        JTagged
    );
    case!(
        constructs_jraw,
        |b| {
            let text = b.intern_text("text");
            b.new_node(View::JRaw { text }, 0)
        },
        JRaw
    );
    case!(
        constructs_jawait,
        |b| {
            let value = leaf(&mut b);
            b.new_node(View::JAwait { value }, 0)
        },
        JAwait
    );
    case!(
        constructs_jspread,
        |b| {
            let value = leaf(&mut b);
            b.new_node(View::JSpread { value }, 0)
        },
        JSpread
    );
    case!(
        constructs_jqualified,
        |b| {
            let path = b.intern_text("module");
            let module = b.import(Import {
                name: Name::new("Module"),
                path,
            });
            let member = b.intern_text("text");
            b.new_node(
                View::JQualified {
                    module,
                    member: Some(member),
                },
                0,
            )
        },
        JQualified
    );
    case!(
        constructs_jnumber,
        |b| {
            let value = b.intern_const(Constant::Int(1));
            b.new_node(View::JNumber { value }, 0)
        },
        JNumber
    );
    case!(
        constructs_jstr,
        |b| {
            let text = b.intern_text("text");
            b.new_node(View::JStr { text }, 0)
        },
        JStr
    );
    case!(constructs_jbool, |b| { b.new_node(View::JBool, 0) }, JBool);
    case!(constructs_jnull, |b| { b.new_node(View::JNull, 0) }, JNull);
    case!(
        constructs_jundefined,
        |b| { b.new_node(View::JUndefined, 0) },
        JUndefined
    );
    case!(
        constructs_jjson,
        |b| {
            let text = b.intern_text("text");
            b.new_node(View::JJson { text }, 0)
        },
        JJson
    );
    case!(
        constructs_jrecordrest,
        |b| {
            let value = leaf(&mut b);
            let info = b.rest_info([]);
            b.new_node(View::JRecordRest { value, info }, 0)
        },
        JRecordRest
    );
    case!(
        constructs_sblock,
        |b| {
            let statements = [leaf(&mut b), leaf(&mut b)];
            b.new_node(
                View::SBlock {
                    statements: &statements,
                },
                0,
            )
        },
        SBlock
    );
    case!(
        constructs_sdecl,
        |b| {
            let var = b.new_var_id(Name::new("v"), 0);
            let value = Some(leaf(&mut b));
            b.new_node(View::SDecl { var, value }, 0)
        },
        SDecl
    );
    case!(
        constructs_sexp,
        |b| {
            let value = leaf(&mut b);
            b.new_node(View::SExp { value }, 0)
        },
        SExp
    );
    case!(
        constructs_sif,
        |b| {
            let condition = leaf(&mut b);
            let then_ = leaf(&mut b);
            let else_ = Some(leaf(&mut b));
            b.new_node(
                View::SIf {
                    condition,
                    then_,
                    else_,
                },
                0,
            )
        },
        SIf
    );
    case!(
        constructs_swhile,
        |b| {
            let condition = leaf(&mut b);
            let body = leaf(&mut b);
            let label = b.intern_text("text");
            b.new_node(
                View::SWhile {
                    condition,
                    body,
                    label: Some(label),
                },
                0,
            )
        },
        SWhile
    );
    case!(
        constructs_sforrange,
        |b| {
            let var = b.new_var_id(Name::new("v"), 0);
            let parts = [leaf(&mut b), leaf(&mut b), leaf(&mut b)];
            let label = b.intern_text("text");
            b.new_node(
                View::SForRange {
                    var,
                    parts: &parts,
                    label: Some(label),
                },
                0,
            )
        },
        SForRange
    );
    case!(
        constructs_sforof,
        |b| {
            let var = b.new_var_id(Name::new("v"), 0);
            let iterable = leaf(&mut b);
            let body = leaf(&mut b);
            b.new_node(
                View::SForOf {
                    var,
                    parts: &[iterable, body],
                    label: None,
                },
                0,
            )
        },
        SForOf
    );
    case!(
        constructs_sforawaitof,
        |b| {
            let var = b.new_var_id(Name::new("v"), 0);
            let iterable = leaf(&mut b);
            let body = leaf(&mut b);
            b.new_node(
                View::SForAwaitOf {
                    var,
                    parts: &[iterable, body],
                    label: None,
                },
                0,
            )
        },
        SForAwaitOf
    );
    case!(
        constructs_sswitch,
        |b| {
            let scrutinee = leaf(&mut b);
            let actions = [leaf(&mut b)];
            let header = b.switch_header(SwitchInput {
                keys: vec![],
                clauses: vec![],
                constants: 0,
                consts_full: false,
                blocks_full: false,
                has_default: true,
                dispatch: SwitchDispatch::Direct,
            });
            b.new_node(
                View::SSwitch {
                    scrutinee,
                    actions: &actions,
                    header,
                },
                0,
            )
        },
        SSwitch
    );
    case!(
        constructs_sreturn,
        |b| {
            let value = leaf(&mut b);
            b.new_node(View::SReturn { value }, 0)
        },
        SReturn
    );
    case!(
        constructs_sthrow,
        |b| {
            let value = leaf(&mut b);
            b.new_node(View::SThrow { value }, 0)
        },
        SThrow
    );
    case!(
        constructs_stry,
        |b| {
            let parts = [leaf(&mut b), leaf(&mut b)];
            let exception = b.new_var_id(Name::new("v"), 0);
            b.new_node(
                View::STry {
                    parts: &parts,
                    exception: Some(exception),
                },
                0,
            )
        },
        STry
    );
    case!(
        constructs_sbreak,
        |b| {
            let label = b.intern_text("text");
            b.new_node(View::SBreak { label: Some(label) }, 0)
        },
        SBreak
    );
    case!(
        constructs_scontinue,
        |b| {
            let label = b.intern_text("text");
            b.new_node(View::SContinue { label: Some(label) }, 0)
        },
        SContinue
    );
    case!(
        constructs_sdebugger,
        |b| { b.new_node(View::SDebugger, 0) },
        SDebugger
    );
    case!(
        constructs_srest,
        |b| {
            let var = b.new_var_id(Name::new("v"), 0);
            let value = leaf(&mut b);
            let info = b.rest_info([]);
            b.new_node(View::SRest { var, value, info }, 0)
        },
        SRest
    );
}

#[cfg(test)]
mod boundary_tests {
    use super::*;
    use crate::lambda::SwitchDispatch;
    use crate::name::Name;

    #[test]
    fn switch_default_multipliers_compose_and_stop_at_full_tables() {
        for (consts_full, blocks_full, count) in [
            (false, false, 4),
            (true, false, 1),
            (false, true, 1),
            (true, true, 1),
        ] {
            let mut b = Bir::default();
            let var = b.new_var_id(Name::new("v"), 0);
            let mut root = b.new_node(View::Var { var }, 0);
            for _ in 0..2 {
                let scrutinee = b.new_node(View::JNull, 0);
                let header = b.switch_header(SwitchInput {
                    keys: vec![],
                    clauses: vec![],
                    constants: 0,
                    consts_full,
                    blocks_full,
                    has_default: true,
                    dispatch: SwitchDispatch::Direct,
                });
                root = b.new_node(
                    View::Switch {
                        scrutinee,
                        actions: &[root],
                        header,
                    },
                    0,
                );
            }
            assert_eq!(b.vars.uses(var), count);
            b.validate(Some(root)).unwrap();
            let copy = b.copy_subtree(root, &[]);
            b.replace(root, copy);
            assert_eq!(b.vars.uses(var), count);
            b.validate(Some(root)).unwrap();
            b.release(root);
            b.validate(None).unwrap();
        }
    }

    #[test]
    fn static_catch_copy_renames_labels_and_params() {
        let mut b = Bir::default();
        let params = b.new_vars(&[Name::new("e")]);
        let var = params.iter().next().unwrap();
        let header = b.catch_header(7, params);
        let arg = b.new_node(View::JNull, 0);
        let body = b.new_node(
            View::Exit {
                label: 7,
                args: &[arg],
            },
            0,
        );
        let handler = b.new_node(View::Var { var }, 0);
        let root = b.new_node(
            View::Catch {
                body,
                handler,
                header,
            },
            0,
        );
        assert_eq!(b.catch(header).uses(), 1);
        let copied = b.copy_subtree(root, &[]);
        let View::Catch {
            header: new_header, ..
        } = b.view(copied)
        else {
            panic!()
        };
        assert_ne!(header, new_header);
        assert_ne!(b.catch(header).label, b.catch(new_header).label);
        assert_eq!(b.catch(new_header).uses(), 1);
        let pair = b.new_node(
            View::Seq {
                first: root,
                second: copied,
            },
            0,
        );
        b.validate(Some(pair)).unwrap();
        b.release(pair);
        assert_eq!(b.catch(header).uses(), 0);
        assert_eq!(b.catch(new_header).uses(), 0);
        b.validate(None).unwrap();
    }

    #[test]
    fn copying_renames_free_uses_but_freshens_local_binders() {
        let mut b = Bir::default();
        let free = b.new_var_id(Name::new("free"), 0);
        let renamed = b.new_var_id(Name::new("renamed"), 1);
        let local = b.new_var_id(Name::new("local"), 2);
        let value = b.new_node(View::Var { var: free }, 0);
        let body = b.new_node(View::Var { var: local }, 0);
        let root = b.new_node(
            View::Let {
                var: local,
                value: Some(value),
                body,
            },
            0,
        );
        let copied = b.copy_subtree(root, &[(free, renamed), (local, renamed)]);
        let View::Let {
            var: copied_local, ..
        } = b.view(copied)
        else {
            panic!()
        };
        assert_ne!(copied_local, local);
        assert_ne!(copied_local, renamed);
        assert_eq!(b.vars.uses(renamed), 1);
        let pair = b.new_node(
            View::Seq {
                first: root,
                second: copied,
            },
            0,
        );
        b.validate(Some(pair)).unwrap();
    }

    #[test]
    #[cfg(debug_assertions)]
    fn sharing_rejected_before_modifying_arena() {
        let mut b = Bir::default();
        let child = b.new_node(View::JNull, 0);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            b.new_node(
                View::Seq {
                    first: child,
                    second: child,
                },
                0,
            )
        }));
        assert!(result.is_err());
        b.validate(Some(child)).unwrap();
    }

    #[test]
    fn effect_and_capture_corruption_are_detected() {
        let mut b = Bir::default();
        let var = b.new_var_id(Name::new("v"), 0);
        let body = b.new_node(View::Var { var }, 0);
        let header = b.function_header(
            VarSpan::default(),
            FunctionAttribute::default(),
            LamLoc::NONE,
        );
        let root = b.new_node(View::Fun { body, header }, 0);
        b.vars.flags[var.index()].0 &= !VarFlags::CAPTURED;
        assert!(
            b.validate(Some(root))
                .unwrap_err()
                .contains("capture")
        );
        b.vars.flags[var.index()].0 |= VarFlags::CAPTURED;
        b.nodes[root.index()].set_flags(NodeFlags(0));
        assert!(
            b.validate(Some(root))
                .unwrap_err()
                .contains("effect")
        );
    }
}

#[cfg(test)]
mod js_metadata_tests {
    use super::*;
    use crate::js_ir::arena::FieldPos;
    use crate::name::Name;

    #[test]
    fn optional_js_operands_round_trip_through_copy() {
        let mut b = Bir::default();
        let body = b.new_node(View::SBlock { statements: &[] }, 0);
        let finaliser = b.new_node(View::SBlock { statements: &[] }, 0);
        let try_ = b.new_node(
            View::STry {
                parts: &[body, finaliser],
                exception: None,
            },
            0,
        );
        let object = b.new_node(View::JNull, 0);
        let property = b.intern_text("field");
        let dot = b.new_node(
            View::JDot {
                object,
                property,
                position: FieldPos::new(Some(123456)),
            },
            0,
        );
        let label = b.new_node(View::SBreak { label: None }, 0);
        let loop_body = b.new_node(
            View::SBlock {
                statements: &[label],
            },
            0,
        );
        let iterable = b.new_node(View::JArray { values: &[] }, 0);
        let var = b.new_var_id(Name::new("item"), 0);
        let loop_ = b.new_node(
            View::SForOf {
                var,
                parts: &[iterable, loop_body],
                label: None,
            },
            0,
        );
        let root = b.new_node(
            View::SBlock {
                statements: &[try_, dot, loop_],
            },
            0,
        );
        b.validate(Some(root)).unwrap();
        let copy = b.copy_subtree(root, &[]);
        b.replace(root, copy);
        b.validate(Some(root)).unwrap();
        let View::SBlock { statements } = b.view(root) else {
            panic!()
        };
        assert!(matches!(
            b.view(statements[0]),
            View::STry {
                exception: None,
                ..
            }
        ));
        let View::JDot { position, .. } = b.view(statements[1]) else {
            panic!()
        };
        assert_eq!(position.get(), Some(123456));
    }

    #[test]
    fn rest_fields_are_binders_and_are_freshened() {
        let mut b = Bir::default();
        let rest = b.new_var_id(Name::new("rest"), 0);
        let field = b.new_var_id(Name::new("field"), 1);
        let name = b.intern_text("field");
        let info = b.rest_info([RestField {
            name,
            binding: Some(field),
        }]);
        let value = b.new_node(View::JNull, 0);
        let decl = b.new_node(
            View::SRest {
                var: rest,
                value,
                info,
            },
            0,
        );
        let usage = b.new_node(View::Var { var: field }, 0);
        let root = b.new_node(
            View::SBlock {
                statements: &[decl, usage],
            },
            0,
        );
        assert_eq!(b.vars.binder(field), Some(decl));
        let copied = b.copy_subtree(root, &[]);
        let View::SBlock { statements } = b.view(copied) else {
            panic!()
        };
        let View::SRest { info, .. } = b.view(statements[0]) else {
            panic!()
        };
        let JsPayload::Rest(fields) = b.javascript(info) else {
            panic!()
        };
        let fresh = b.rest_fields(*fields)[0].binding.unwrap();
        assert_ne!(fresh, field);
        assert_eq!(b.vars.binder(fresh), Some(statements[0]));
        let pair = b.new_node(
            View::SBlock {
                statements: &[root, copied],
            },
            0,
        );
        b.validate(Some(pair)).unwrap();
    }

    #[test]
    fn methods_keep_their_representation_when_copied() {
        let mut b = Bir::default();
        let body = b.new_node(View::SBlock { statements: &[] }, 0);
        let header = b.method_header(
            VarSpan::default(),
            FunctionAttribute::default(),
            LamLoc::NONE,
        );
        let root = b.new_node(View::JFun { body, header }, 0);
        let copied = b.copy_subtree(root, &[]);
        let View::JFun { header, .. } = b.view(copied) else {
            panic!()
        };
        assert_eq!(
            b.function(header).flags & FuncHeader::METHOD,
            FuncHeader::METHOD
        );
        let pair = b.new_node(
            View::JArray {
                values: &[root, copied],
            },
            0,
        );
        b.validate(Some(pair)).unwrap();
    }
}

#[cfg(test)]
mod cost_measurements {
    use super::*;
    use crate::name::Name;
    #[test]
    fn sampled_edit_costs() {
        let mut b = Bir::default();
        let leaf = b.new_node(View::JNull, 0);
        let mut root = leaf;
        for i in 0..1000 {
            let var = b.new_var_id(Name::new("x"), i);
            let value = b.new_node(View::JNull, 0);
            root = b.new_node(
                View::Let {
                    var,
                    value: Some(value),
                    body: root,
                },
                0,
            );
        }
        println!("COST build 2001 nodes: {} visits", b.steps.get());
        b.steps.set(0);
        for _ in 0..100 {
            let new = b.new_node(View::JNull, 0);
            b.replace(leaf, new);
        }
        println!(
            "COST replace 100 times at depth 1000: {} visits",
            b.steps.get()
        );
        b.validate(Some(root)).unwrap();
        let mut b = Bir::default();
        for i in 0..5000 {
            b.intern_text(&format!("symbol_{i}"));
        }
        for i in 0..5000 {
            b.intern_text(&format!("symbol_{i}"));
        }
        println!(
            "COST intern 5000 distinct strings twice: {} comparisons",
            b.intern_comparisons.get()
        );
    }
}

#[cfg(test)]
mod incremental_cost_tests {
    use super::*;
    use crate::name::Name;

    fn chain(b: &mut Bir, depth: u32) -> (NodeId, NodeId) {
        let leaf = b.new_node(View::JNull, 0);
        let mut root = leaf;
        for i in 0..depth {
            let var = b.new_var_id(Name::new("x"), i);
            let value = b.new_node(View::JNull, 0);
            root = b.new_node(
                View::Let {
                    var,
                    value: Some(value),
                    body: root,
                },
                0,
            );
        }
        (root, leaf)
    }

    #[test]
    fn hundred_thousand_nodes_have_linear_construction_cost() {
        let mut b = Bir::for_typed_exprs(100_000);
        let (root, _) = chain(&mut b, 49_999);
        let root = b.new_node(View::SExp { value: root }, 0);
        assert_eq!(b.nodes.len(), 100_000);
        let steps = b.steps.get();
        println!("COST build 100000 nodes: {steps} visits (bound 24*n)");
        assert!(steps <= 24 * 100_000, "{steps} visits");
        b.validate(Some(root)).unwrap();
    }

    #[test]
    fn ten_thousand_leaf_replacements_do_not_walk_the_ten_thousand_deep_spine() {
        let mut b = Bir::default();
        let (root, leaf) = chain(&mut b, 10_000);
        b.steps.set(0);
        for _ in 0..10_000 {
            let new = b.new_node(View::JNull, 0);
            b.replace(leaf, new);
        }
        let steps = b.steps.get();
        println!("COST replace 10000 times at depth 10000: {steps} visits (bound 64*n)");
        assert!(steps <= 64 * 10_000, "{steps} visits");
        b.validate(Some(root)).unwrap();
    }

    #[test]
    fn weighted_module_leaf_replacements_do_not_walk_the_spine() {
        let mut b = Bir::default();
        let (root, leaf) = chain(&mut b, 10_000);
        let View::Let {
            value: Some(value), ..
        } = b.view(root)
        else {
            panic!()
        };
        let scrutinee = b.new_node(View::JNull, 0);
        let default = b.new_node(View::JNull, 0);
        let header = b.switch_header(SwitchInput {
            keys: vec![],
            clauses: vec![],
            constants: 0,
            consts_full: false,
            blocks_full: false,
            has_default: true,
            dispatch: crate::lambda::SwitchDispatch::Direct,
        });
        let switch = b.new_node(
            View::Switch {
                scrutinee,
                actions: &[default],
                header,
            },
            0,
        );
        b.replace(value, switch);
        b.validate(Some(root)).unwrap();
        assert_eq!(b.weighted_switches, 1);
        assert_eq!(b.weights[leaf.index()], 0);
        b.steps.set(0);
        for _ in 0..10_000 {
            let new = b.new_node(View::JNull, 0);
            b.replace(leaf, new);
        }
        let steps = b.steps.get();
        println!(
            "COST weighted-module replace 10000 times at depth 10000: {steps} visits (bound 64*n)"
        );
        assert!(steps <= 64 * 10_000, "{steps} visits");
        b.validate(Some(root)).unwrap();
    }

    #[test]
    fn fifty_thousand_distinct_strings_have_linear_lookup_comparisons() {
        let mut b = Bir::default();
        let ids: Vec<_> = (0..50_000)
            .map(|i| b.intern_text(&format!("symbol_{i}")))
            .collect();
        for (i, &id) in ids.iter().enumerate() {
            assert_eq!(b.intern_text(&format!("symbol_{i}")), id);
        }
        let comparisons = b.intern_comparisons.get();
        println!("COST intern 50000 distinct strings twice: {comparisons} comparisons (bound 3*n)");
        assert!(comparisons <= 3 * 50_000, "{comparisons} comparisons");
    }

    #[test]
    fn moved_free_uses_cross_capture_boundaries_without_per_use_parent_walks() {
        let mut b = Bir::default();
        let free = b.new_var_id(Name::new("free"), 0);
        let body = b.new_node(View::JNull, 0);
        let header = b.function_header(
            VarSpan::default(),
            FunctionAttribute::default(),
            LamLoc::NONE,
        );
        let root = b.new_node(View::Fun { body, header }, 0);
        let uses: Vec<_> = (0..10_000)
            .map(|_| b.new_node(View::Var { var: free }, 0))
            .collect();
        let replacement = b.new_node(View::JArray { values: &uses }, 0);
        b.steps.set(0);
        b.replace(body, replacement);
        assert!(b.vars.flags(free).contains(VarFlags::CAPTURED));
        assert!(b.steps.get() < 25 * 10_000);
        b.validate(Some(root)).unwrap();
    }

    #[test]
    fn hashed_payloads_preserve_float_spelling_and_primitive_identity() {
        use std::hash::{Hash, Hasher};
        let mut b = Bir::default();
        let pos = b.intern_float("0.").unwrap();
        let neg = b.intern_float("-0.").unwrap();
        assert_ne!(pos, neg);
        let id = b.intern_float("nan").unwrap();
        assert_eq!(id, b.intern_float("nan").unwrap());
        assert_ne!(id, b.intern_float("NaN").unwrap());
        let nan = b.constant(id);
        let Constant::Float(value) = nan else {
            panic!("not a float")
        };
        assert!(value.value().is_nan());
        let mut h1 = std::collections::hash_map::DefaultHasher::new();
        let mut h2 = std::collections::hash_map::DefaultHasher::new();
        nan.hash(&mut h1);
        nan.hash(&mut h2);
        assert_eq!(h1.finish(), h2.finish());
        let prim = PrimPayload {
            primitive: Primitive::Paddint,
            loc: LamLoc::NONE,
        };
        let id = b.intern_prim(prim.clone());
        for _ in 0..10_000 {
            assert_eq!(b.intern_prim(prim.clone()), id);
        }
        assert_ne!(
            id,
            b.intern_prim(PrimPayload {
                primitive: Primitive::Psubint,
                loc: LamLoc::NONE
            })
        );
    }

    #[test]
    fn catch_labels_are_indexed_and_weights_are_cached_between_queries() {
        let mut b = Bir::default();
        for label in 0..10_000 {
            b.catch_header(label, VarSpan::default());
        }
        let root = b.new_node(
            View::Exit {
                label: 9999,
                args: &[],
            },
            0,
        );
        b.validate(Some(root)).unwrap();
        b.release(root);
        b.validate(None).unwrap();
        let (body, leaf) = chain(&mut b, 1000);
        let scrutinee = b.new_node(View::JNull, 0);
        let header = b.switch_header(SwitchInput {
            keys: vec![],
            clauses: vec![],
            constants: 0,
            consts_full: false,
            blocks_full: false,
            has_default: true,
            dispatch: crate::lambda::SwitchDispatch::Direct,
        });
        let root = b.new_node(
            View::Switch {
                scrutinee,
                actions: &[body],
                header,
            },
            0,
        );
        assert_eq!(b.weight(leaf), 2);
        b.steps.set(0);
        for _ in 0..10_000 {
            assert_eq!(b.weight(leaf), 2);
        }
        assert_eq!(b.steps.get(), 10_000);
        b.validate(Some(root)).unwrap();
        b.release(root);
        assert_eq!(b.weighted_switches, 0);
        b.validate(None).unwrap();
    }
}

#[cfg(test)]
mod bulk_tests {
    use super::*;

    #[test]
    fn four_thousand_nested_functions_are_linear() {
        let mut bir = Bir::default();
        bir.begin_bulk();
        let free = bir.new_var_id(Name::new("free"), 0);
        let mut root = bir.new_node(View::Var { var: free }, 0);
        for _ in 0..4_000 {
            let header = bir.function_header(
                VarSpan::default(), FunctionAttribute::default(), LamLoc::NONE,
            );
            root = bir.new_node(View::Fun { body: root, header }, 0);
        }
        bir.finish_bulk(root);
        let steps = bir.steps.get();
        println!("bulk 4001 nodes: {steps} steps");
        assert!(steps <= 40 * 4_001, "{steps}");
        assert!(bir.vars.flags(free).contains(VarFlags::CAPTURED));
        bir.validate(Some(root)).unwrap();
    }

    fn sample(seed: u64, bulk: bool) -> Bir {
        let mut b = Bir::default();
        if bulk { b.begin_bulk(); }
        let vars = b.new_vars(&[Name::new("outer"), Name::new("inner")]);
        let free = b.new_var_id(Name::new("free"), 2);
        let mut state = seed;
        let mut root = b.new_node(View::Var { var: free }, 0);
        for _ in 0..30 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let var = if state & 1 == 0 { free } else { vars.iter().next().unwrap() };
            let use_ = b.new_node(View::Var { var }, 0);
            root = match state >> 32 & 3 {
                0 => b.new_node(View::While { condition: use_, body: root }, 0),
                1 => b.new_node(View::Seq { first: use_, second: root }, 0),
                _ => {
                    let body = b.new_node(View::Seq { first: use_, second: root }, 0);
                    let header = b.function_header(
                        VarSpan::default(), FunctionAttribute::default(), LamLoc::NONE,
                    );
                    b.new_node(View::Fun { body, header }, 0)
                }
            };
        }
        let header = b.function_header(vars, FunctionAttribute::default(), LamLoc::NONE);
        root = b.new_node(View::Fun { body: root, header }, 0);
        if bulk { b.finish_bulk(root); }
        b.validate(Some(root)).unwrap();
        b
    }

    #[test]
    fn seeded_bulk_captures_match_incremental() {
        for seed in 0..100 {
            let bulk = sample(seed, true);
            let incremental = sample(seed, false);
            assert_eq!(bulk.vars.flags, incremental.vars.flags, "seed {seed}");
        }
    }
}

#[cfg(test)]
mod local_weight_tests {
    use super::*;
    use crate::lambda::SwitchDispatch;
    use crate::name::Name;

    fn weighted(b: &mut Bir, default: NodeId) -> NodeId {
        let scrutinee = b.new_node(View::JNull, 0);
        let header = b.switch_header(SwitchInput {
            keys: vec![],
            clauses: vec![],
            constants: 0,
            consts_full: false,
            blocks_full: false,
            has_default: true,
            dispatch: SwitchDispatch::Direct,
        });
        b.new_node(
            View::Switch {
                scrutinee,
                actions: &[default],
                header,
            },
            0,
        )
    }

    #[test]
    fn switch_edits_preserve_unrelated_caches_and_clear_only_moved_weights() {
        let mut b = Bir::default();
        let var = b.new_var_id(Name::new("free"), 0);
        let left_use = b.new_node(View::Var { var }, 0);
        let left = weighted(&mut b, left_use);
        let moved = b.new_node(View::Var { var }, 0);
        assert_eq!(b.weight(left_use), 2);
        assert_eq!(b.weight(moved), 1);

        // Creating another weighted switch invalidates its default, not left.
        let right = weighted(&mut b, moved);
        assert_eq!(b.weights[left_use.index()], 2);
        assert_eq!(b.weights[moved.index()], 0);
        assert_eq!(b.weight(moved), 2);
        let root = b.new_node(
            View::Seq {
                first: left,
                second: right,
            },
            0,
        );
        b.validate(Some(root)).unwrap();
        assert_eq!(b.vars.uses(var), 4);

        // Promote the default out of its weighted parent: the surviving slot
        // keeps weight 1, whereas the old default's slot becomes free.
        b.replace(right, moved);
        assert_eq!(b.weights[left_use.index()], 2);
        assert_eq!(b.weights[right.index()], 1);
        assert_eq!(b.weights[moved.index()], 0);
        assert_eq!(b.vars.uses(var), 3);
        b.validate(Some(root)).unwrap();

        // Slot reuse starts unknown, even when that slot used to have weight 2.
        let reused = b.new_node(View::Var { var }, 0);
        assert_eq!(reused, moved);
        assert_eq!(b.weights[reused.index()], 0);
        let new_switch = weighted(&mut b, reused);
        b.replace(right, new_switch);
        assert_eq!(b.weights[left_use.index()], 2);
        assert_eq!(b.weights[reused.index()], 0);
        assert_eq!(b.weight(reused), 2);
        assert_eq!(b.vars.uses(var), 4);
        b.validate(Some(root)).unwrap();

        // Replacing a switch by an ordinary node and releasing its old default
        // must not invalidate a cached default in a different subtree.
        let plain = b.new_node(View::JNull, 0);
        b.replace(right, plain);
        assert_eq!(b.weights[left_use.index()], 2);
        assert_eq!(b.weights[reused.index()], 0);
        assert_eq!(b.vars.uses(var), 2);
        b.validate(Some(root)).unwrap();
        b.release(root);
        b.validate(None).unwrap();
    }

    #[test]
    fn nested_default_promotion_reweights_descendants_without_touching_siblings() {
        let mut b = Bir::default();
        let var = b.new_var_id(Name::new("v"), 0);
        let inner_use = b.new_node(View::Var { var }, 0);
        let inner = weighted(&mut b, inner_use);
        let outer = weighted(&mut b, inner);
        let sibling = b.new_node(View::Var { var }, 0);
        let root = b.new_node(
            View::Seq {
                first: outer,
                second: sibling,
            },
            0,
        );
        assert_eq!(b.weight(inner_use), 4);
        assert_eq!(b.weight(sibling), 1);
        assert_eq!(b.vars.uses(var), 5);
        b.replace(outer, inner);
        assert_eq!(b.weights[sibling.index()], 1);
        assert_eq!(b.weights[outer.index()], 1);
        assert_eq!(b.weights[inner_use.index()], 0);
        assert_eq!(b.weight(inner_use), 2);
        assert_eq!(b.vars.uses(var), 3);
        b.validate(Some(root)).unwrap();
    }

    #[test]
    fn count_release_and_weight_walks_reuse_their_buffers() {
        let mut b = Bir::default();
        let values: Vec<_> = (0..100).map(|_| b.new_node(View::JNull, 0)).collect();
        let mut root = b.new_node(View::JArray { values: &values }, 0);
        root = weighted(&mut b, root);
        let count_buffer = b.count_stack.as_ptr();
        let count_capacity = b.count_stack.capacity();
        assert!(count_capacity >= values.len());
        for _ in 0..10 {
            b.adjust_counts(root, 0);
            assert!(b.count_stack.is_empty());
            assert_eq!(b.count_stack.as_ptr(), count_buffer);
            assert_eq!(b.count_stack.capacity(), count_capacity);
        }
        b.weight(values[0]);
        let weight_buffer = b.weight_path.as_ptr();
        let weight_capacity = b.weight_path.capacity();
        assert!(weight_capacity > 0);
        for &id in &values[1..] {
            b.weight(id);
        }
        assert!(b.weight_path.is_empty());
        assert_eq!(b.weight_path.as_ptr(), weight_buffer);
        assert_eq!(b.weight_path.capacity(), weight_capacity);
        b.release(root);
        let release_buffer = b.release_stack.as_ptr();
        let release_capacity = b.release_stack.capacity();
        assert!(release_capacity >= values.len());
        let values: Vec<_> = (0..100).map(|_| b.new_node(View::JNull, 0)).collect();
        let root = b.new_node(View::JArray { values: &values }, 0);
        b.release(root);
        assert!(b.release_stack.is_empty());
        assert_eq!(b.release_stack.as_ptr(), release_buffer);
        assert_eq!(b.release_stack.capacity(), release_capacity);
        b.validate(None).unwrap();
    }
}
