//! Dormant backend IR: packed mutable trees with module-local typed pools.
//!
//! Constructors consume detached roots. A finished unit has one root; temporary
//! forests are permitted while building an edit. `validate` checks a finished
//! tree, including all allocated slots. Handles belong to one arena and become
//! invalid when released (slots are reused). No compiler pipeline uses this IR.
//! `TAIL` and function self-tail-call flags are valid only after explicitly
//! running `mark_tail_positions`; edits invalidate that analysis.
//!
//! Ordinary constructors touch direct operands. Capture boundaries inspect their
//! captured subtree; attaching a doubled switch default updates its affected use
//! counts. Replacement visits removed/replacement subtrees, stops effect/fact
//! repair at the first unchanged ancestor, and walks the capture ancestor chain
//! at most once when new uncaptured free uses require it.
pub mod bridge;
mod dump;
mod edit;
mod node;
mod pools;
mod validate;
mod vars;

use crate::lambda::{ApInfo, FunctionAttribute, LamLoc};
use crate::name::Name;
pub use node::{Node, NodeFlags, Op, View};
pub use pools::*;
pub use vars::*;

/// One compilation unit. Parent links support local ancestor repair after edits.
#[derive(Default)]
pub struct Bir {
    nodes: Vec<Node>,
    parents: Vec<Option<NodeId>>,
    cold: Vec<Option<ColdId>>,
    lists: Lists,
    vars: VarTable,
    pools: Pools,
    exports: Vec<(VarId, Name)>,
    free_nodes: Vec<NodeId>,
    death_candidates: Vec<NodeId>,
    func_owners: Vec<Option<NodeId>>,
    capture_boundaries: usize,
    weighted_switches: usize,
    // Zero is unknown; every valid use weight is positive. Cache invalidation
    // follows only the affected subtree, never an unrelated module-wide epoch.
    weights: Vec<u32>,
    weight_path: Vec<(NodeId, u32)>,
    count_stack: Vec<(NodeId, i64)>,
    release_stack: Vec<(NodeId, u32)>,
    capture_epoch: u64,
    capture_binders: Vec<u64>,
    capture_chain: Vec<(u64, bool)>,
    capture_stack: Vec<NodeId>,
    capture_uses: Vec<VarId>,
    tails_valid: bool,
    bulk: bool,
    bulk_binders: Vec<(u64, u32)>,
    #[cfg(test)]
    steps: std::cell::Cell<u64>,
    #[cfg(test)]
    intern_comparisons: std::cell::Cell<u64>,
}
impl Bir {
    #[inline]
    fn visit(&self) {
        #[cfg(test)]
        self.steps.set(self.steps.get() + 1);
    }
    #[inline]
    fn compare_interned(&self) {
        #[cfg(test)]
        self.intern_comparisons
            .set(self.intern_comparisons.get() + 1);
    }
    /// Reserve the hot arrays using a typed-expression count.
    pub fn for_typed_exprs(count: usize) -> Self {
        Self {
            nodes: Vec::with_capacity(count),
            parents: Vec::with_capacity(count),
            ..Self::default()
        }
    }
    /// Read a live packed node.
    pub fn node(&self, id: NodeId) -> Node {
        self.visit();
        let node = self.nodes[id.index()];
        assert_ne!(node.op(), Op::Free, "released Bir handle");
        node
    }
    /// Decode typed operands without exposing writable node storage.
    pub fn view(&self, id: NodeId) -> View<'_> {
        self.node(id).view(&self.lists)
    }
    /// Variable data, read-only.
    pub fn vars(&self) -> &VarTable {
        &self.vars
    }
    /// Source metadata, when present.
    pub fn cold(&self, id: NodeId) -> Option<Cold> {
        self.node(id);
        self.cold
            .get(id.index())
            .copied()
            .flatten()
            .map(|c| self.pools.cold[c.index()])
    }
    /// Attach source metadata, lazily allocating the parallel cold array.
    pub fn set_cold(&mut self, id: NodeId, cold: Cold) {
        self.node(id);
        let entry = ColdId(index(self.pools.cold.len()));
        self.pools.cold.push(cold);
        self.cold.resize(self.nodes.len(), None);
        self.cold[id.index()] = Some(entry);
        let mut flags = self.nodes[id.index()].flags();
        flags.0 |= NodeFlags::HAS_LOC;
        self.nodes[id.index()].set_flags(flags);
    }
    /// Allocate a variable with an explicit naming order.
    pub fn new_var_id(&mut self, name: Name, order: u32) -> VarId {
        let id = VarId(index(self.vars.len()));
        self.capture_binders.push(0);
        self.bulk_binders.push((0, 0));
        self.vars.name.push(name);
        self.vars.order.push(order);
        self.vars.flags.push(VarFlags::default());
        self.vars.uses.push(0);
        self.vars.binder.push(None);
        self.vars.fact.push(Fact::Unknown);
        self.vars.printed.push(None);
        id
    }
    /// Allocate a contiguous run of fresh parameters/binders.
    pub fn new_vars(&mut self, names: &[Name]) -> VarSpan {
        let start = index(self.vars.len());
        for &name in names {
            self.new_var_id(name, index(self.vars.len()));
        }
        VarSpan {
            start,
            len: index(names.len()),
        }
    }
    /// Add an export in output order.
    pub fn export(&mut self, var: VarId, name: Name) {
        self.vars.flags[var.index()].0 |= VarFlags::EXPORTED;
        self.exports.push((var, name));
    }
    /// Exports in insertion order.
    pub fn exports(&self) -> &[(VarId, Name)] {
        &self.exports
    }
    /// Store the naming pass's chosen spelling.
    pub fn set_printed(&mut self, var: VarId, name: Name) {
        self.vars.printed[var.index()] = Some(name);
    }
    /// Mark an external JavaScript variable (it has no local binder).
    pub fn mark_js_global(&mut self, var: VarId) {
        self.vars.flags[var.index()].0 |= VarFlags::JS_GLOBAL;
    }
    /// Intern text in the module's contiguous text buffer.
    pub fn intern_text(&mut self, text: &str) -> StrId {
        let hash = self.pools.hash_builder.hash_one(text);
        if let Some(&(_, id)) = self.pools.text_index.find(hash, |&(_, id)| {
            self.compare_interned();
            self.text(id) == text
        }) {
            return id;
        }
        let id = StrId(index(self.pools.strings.len()));
        self.pools
            .strings
            .push((index(self.pools.text.len()), index(text.len())));
        self.pools.text.push_str(text);
        self.pools
            .text_index
            .insert_unique(hash, (hash, id), |&(hash, _)| hash);
        id
    }
    /// Borrow interned text.
    pub fn text(&self, id: StrId) -> &str {
        let (start, len) = self.pools.strings[id.index()];
        &self.pools.text[start as usize..(start + len) as usize]
    }
    /// Intern a constant. Compound fields must already exist.
    pub fn intern_const(&mut self, value: Constant) -> ConstId {
        let key = value.key();
        let hash = self.pools.hash_builder.hash_one(&key);
        if let Some(&(_, id)) = self.pools.const_index.find(hash, |&(_, id)| {
            self.compare_interned();
            self.pools.const_keys[id.index()] == key
        }) {
            return id;
        }
        let id = ConstId(index(self.pools.consts.len()));
        self.pools.consts.push(value);
        self.pools.const_keys.push(key);
        self.pools
            .const_index
            .insert_unique(hash, (hash, id), |&(hash, _)| hash);
        id
    }
    /// Store flat compound-constant fields.
    pub fn const_fields(&mut self, values: &[ConstId]) -> ConstSpan {
        for v in values {
            assert!(v.index() < self.pools.consts.len());
        }
        let hash = self.pools.hash_builder.hash_one(values);
        if let Some(&(_, span)) = self.pools.const_fields_index.find(hash, |&(_, span)| {
            self.compare_interned();
            self.constant_fields(span) == values
        }) {
            return span;
        }
        let span = ConstSpan {
            start: index(self.pools.const_fields.len()),
            len: index(values.len()),
        };
        self.pools.const_fields.extend_from_slice(values);
        self.pools
            .const_fields_index
            .insert_unique(hash, (hash, span), |&(hash, _)| hash);
        span
    }
    /// Read a constant.
    pub fn constant(&self, id: ConstId) -> &Constant {
        &self.pools.consts[id.index()]
    }
    /// Intern a primitive and its location.
    pub fn intern_prim(&mut self, payload: PrimPayload) -> PrimId {
        let key = payload.key();
        let hash = self.pools.hash_builder.hash_one(&key);
        if let Some(&(_, id)) = self.pools.prim_index.find(hash, |&(_, id)| {
            self.compare_interned();
            self.pools.prim_keys[id.index()] == key
        }) {
            return id;
        }
        let id = PrimId(index(self.pools.prims.len()));
        self.pools.prims.push(payload);
        self.pools.prim_keys.push(key);
        self.pools
            .prim_index
            .insert_unique(hash, (hash, id), |&(hash, _)| hash);
        id
    }
    /// Read a primitive payload.
    pub fn primitive(&self, id: PrimId) -> &PrimPayload {
        &self.pools.prims[id.index()]
    }
    /// Read application metadata.
    pub fn application(&self, id: ApplyId) -> &ApInfo {
        &self.pools.apply[id.index()]
    }
    /// Read JavaScript shape metadata.
    pub fn javascript(&self, id: JsId) -> &JsPayload {
        &self.pools.js[id.index()]
    }
    /// Read a compound constant's fields.
    pub fn constant_fields(&self, span: ConstSpan) -> &[ConstId] {
        &self.pools.const_fields[span.start as usize..(span.start + span.len) as usize]
    }
    /// Imports in encounter order.
    pub fn imports(&self) -> &[Import] {
        &self.pools.imports
    }
    /// Allocate a function header; a header is owned by one function node.
    pub fn function_header(
        &mut self,
        params: VarSpan,
        attr: FunctionAttribute,
        loc: LamLoc,
    ) -> FuncId {
        let id = FuncId(index(self.pools.funcs.len()));
        let attr_id = index(self.pools.attrs.len());
        self.pools.attrs.push(attr);
        self.func_owners.push(None);
        self.pools.funcs.push(FuncHeader {
            params,
            attr: attr_id,
            loc,
            flags: 0,
        });
        id
    }
    /// Allocate a JavaScript method header, which preserves the `this` binding.
    pub fn method_header(
        &mut self,
        params: VarSpan,
        attr: FunctionAttribute,
        loc: LamLoc,
    ) -> FuncId {
        let id = self.function_header(params, attr, loc);
        self.pools.funcs[id.index()].flags |= FuncHeader::METHOD;
        id
    }
    /// Read a function header.
    pub fn function(&self, id: FuncId) -> &FuncHeader {
        &self.pools.funcs[id.index()]
    }
    /// Read a function's cold attributes.
    pub fn function_attributes(&self, id: FuncId) -> &FunctionAttribute {
        &self.pools.attrs[self.function(id).attr as usize]
    }
    /// Allocate switch metadata.
    pub fn switch_header(&mut self, header: SwitchHeader) -> SwitchId {
        assert!(header.constants as usize <= header.keys.len());
        let id = SwitchId(index(self.pools.switches.len()));
        self.pools.switches.push(header);
        id
    }
    /// Read switch metadata.
    pub fn switch(&self, id: SwitchId) -> &SwitchHeader {
        &self.pools.switches[id.index()]
    }
    /// Allocate a static catch header.
    pub fn catch_header(&mut self, label: u32, params: VarSpan) -> CatchId {
        assert!(
            !self.pools.catch_labels.contains_key(&label),
            "duplicate static label"
        );
        let id = CatchId(index(self.pools.catches.len()));
        self.pools.catch_labels.insert(label, id);
        self.pools.next_label = self.pools.next_label.max(u64::from(label) + 1);
        self.pools.catches.push(CatchHeader {
            label,
            params,
            uses: 0,
        });
        id
    }
    /// Read catch metadata and its current exit count.
    pub fn catch(&self, id: CatchId) -> &CatchHeader {
        &self.pools.catches[id.index()]
    }
    /// Allocate application metadata.
    pub fn apply_info(&mut self, info: ApInfo) -> ApplyId {
        let id = ApplyId(index(self.pools.apply.len()));
        self.pools.apply.push(info);
        id
    }
    /// Allocate cold JavaScript shape metadata.
    pub fn js_info(&mut self, info: JsPayload) -> JsId {
        let id = JsId(index(self.pools.js.len()));
        self.pools.js.push(info);
        id
    }
    /// Intern a module reference in first-use order.
    pub fn import(&mut self, module: Import) -> ImportId {
        let hash = self.pools.hash_builder.hash_one(&module);
        if let Some(&(_, id)) = self.pools.import_index.find(hash, |&(_, id)| {
            self.compare_interned();
            self.pools.imports[id.index()] == module
        }) {
            return id;
        }
        let id = ImportId(index(self.pools.imports.len()));
        self.pools.imports.push(module);
        self.pools
            .import_index
            .insert_unique(hash, (hash, id), |&(hash, _)| hash);
        id
    }
}
