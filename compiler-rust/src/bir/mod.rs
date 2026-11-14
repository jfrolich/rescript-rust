//! Dormant backend IR: packed mutable trees with module-local typed pools.
//!
//! Constructors consume detached roots. A finished unit has one root; temporary
//! forests are permitted while building an edit. `validate` checks a finished
//! tree, including all allocated slots. Handles belong to one arena and become
//! invalid when released (slots are reused). No compiler pipeline uses this IR.
//!
//! Ordinary constructors touch direct operands. Capture boundaries inspect their
//! captured subtree; attaching a doubled switch default updates its affected use
//! counts. Replacement visits removed/replacement subtrees, stops effect/fact
//! repair at the first unchanged ancestor, and walks the capture ancestor chain
//! at most once when new uncaptured free uses require it.
pub mod bridge;
pub mod bridge_j;
pub mod engine;
pub mod l;
pub mod j;
pub mod lower;
pub(crate) mod untagged_plan;
pub mod replay;
pub mod shadow;
mod dump;
mod dense;
mod edit;
mod node;
mod pools;
mod validate;
mod tail_facts;
mod vars;

use crate::lambda::{ApInfo, FunctionAttribute, LamLoc};
use crate::name::Name;
pub use node::{Node, NodeFlags, Op, View};
pub use pools::*;
pub use vars::*;

/// One compilation unit. Parent links support local ancestor repair after edits.
#[derive(Default)]
pub struct Bir {
    /// Logical normalisation costs for the opt-in J backend.
    pub j_stats: j::Stats,
    // Mutable normalizer callers explicitly lend this retained worklist.
    j_equal_work: Vec<(NodeId, NodeId)>,
    j_template_scratch: j::norm::TemplateScratch,
    nodes: Vec<Node>,
    parents: Vec<Option<NodeId>>,
    cold: Vec<Option<ColdId>>,
    lists: Lists,
    vars: VarTable,
    pools: Pools,
    exports: Vec<(VarId, Name)>,
    free_nodes: Vec<NodeId>,
    js_scope: Option<lower::scope::Scope>,
    /// X:60 event-argument duplicability, maintained with construction facts.
    j_duplicable: Vec<bool>,
    death_candidates: Vec<NodeId>,
    deaths_deferred: bool,
    func_owners: Vec<Option<NodeId>>,
    tail_candidates: Vec<tail_facts::Candidates>,
    tail_calls: Vec<tail_facts::Candidate>,
    self_tail: Vec<bool>,
    loop_facts: Vec<tail_facts::LoopFacts>,
    capture_boundaries: usize,
    weighted_switches: usize,
    // Zero is unknown; every valid use weight is positive. Cache invalidation
    // follows only the affected subtree, never an unrelated module-wide epoch.
    weights: Vec<u32>,
    weight_path: Vec<(NodeId, u32)>,
    count_stack: Vec<(NodeId, i64)>,
    release_stack: Vec<(NodeId, u32)>,
    effect_work: Vec<NodeId>,
    #[cfg(debug_assertions)]
    checked_children: Vec<u32>,
    #[cfg(debug_assertions)]
    child_epoch: u32,
    capture_epoch: u64,
    capture_binders: Vec<u64>,
    capture_chain: Vec<(u64, bool)>,
    capture_stack: Vec<NodeId>,
    capture_uses: Vec<VarId>,
    bulk: bool,
    bulk_binders: Vec<(u64, u32)>,
    #[cfg(test)]
    steps: std::cell::Cell<u64>,
    #[cfg(test)]
    loop_fact_folds: std::cell::Cell<u64>,
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
        self.vars.j_origin.push(id);
        self.vars.name.push(name);
        self.vars.order.push(order);
        self.vars.flags.push(VarFlags::default());
        self.vars.uses.push(0);
        self.vars.binder.push(None);
        self.vars.fact.push(Fact::Unknown);
        self.vars.printed.push(None);
        if let Some(scope) = &mut self.js_scope {
            scope.push();
            scope.names.variable();
        }
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
    /// Mark the reference `node` as shadowed: it prints as
    /// `globalThis.name` (`lower::globals`). One write.
    pub(crate) fn qualify_global(&mut self, node: NodeId) {
        self.nodes[node.index()].set_var_qualified();
    }
    /// Whether the reference `node` prints as `globalThis.name`. One read.
    pub(crate) fn global_qualified(&self, node: NodeId) -> bool {
        self.node(node).var_qualified()
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
    /// Intern a float with one hash lookup of its spelling (text interning).
    /// A dense string-indexed cache avoids a second constant hash lookup and
    /// parses each spelling once. Reading its value is one constant-array read.
    pub fn intern_float(&mut self, spelling: &str) -> Result<ConstId, bridge::Unsupported> {
        let text = self.intern_text(spelling);
        self.pools.floats.resize(self.pools.strings.len(), None);
        if let Some(id) = self.pools.floats[text.index()] {
            return Ok(id);
        }
        let value = crate::ocaml_float::float_of_string(spelling)
            .ok_or(bridge::Unsupported("invalid float constant spelling"))?;
        Ok(self.intern_const(Constant::Float(FloatConstant {
            spelling: text,
            bits: value.to_bits(),
        })))
    }
    /// Intern a constant in O(encoded payload bytes), using retained encoding
    /// scratch and a flat key-byte pool. Compound fields must already exist.
    pub fn intern_const(&mut self, value: Constant) -> ConstId {
        if let Constant::Float(ref float) = value {
            self.pools.floats.resize(self.pools.strings.len(), None);
            if let Some(id) = self.pools.floats[float.spelling.index()] {
                return id;
            }
            let id = ConstId(index(self.pools.consts.len()));
            self.pools.floats[float.spelling.index()] = Some(id);
            self.pools.consts.push(value);
            self.pools.const_keys.push((0, 0));
            return id;
        }
        let mut key = std::mem::take(&mut self.pools.const_key_scratch);
        crate::binser::to_vec_reuse(&value, &mut key).expect("Bir constant serialization");
        let hash = self.pools.hash_builder.hash_one(&key);
        if let Some(&(_, id)) = self.pools.const_index.find(hash, |&(_, id)| {
            self.compare_interned();
            let (start, len) = self.pools.const_keys[id.index()];
            self.pools.const_key_bytes[start as usize..(start + len) as usize] == key
        }) {
            key.clear();
            self.pools.const_key_scratch = key;
            return id;
        }
        let id = ConstId(index(self.pools.consts.len()));
        self.pools.consts.push(value);
        let start = index(self.pools.const_key_bytes.len());
        let len = index(key.len());
        start.checked_add(len).expect("constant key pool capacity");
        self.pools.const_key_bytes.extend_from_slice(&key);
        self.pools.const_keys.push((start, len));
        key.clear();
        self.pools.const_key_scratch = key;
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
    /// Borrow a block shape, including metadata shared with the source IR.
    pub fn block_tag(&self, info: JsId) -> &crate::lambda::TagInfo {
        match self.javascript(info) {
            JsPayload::Block(tag) => tag,
            JsPayload::ConstantBlock(id) => {
                let Constant::Block { tag, .. } = self.constant(*id) else { panic!("constant block shape") };
                tag
            }
            _ => panic!("block shape metadata"),
        }
    }
    /// Borrow immutable template quasis by their unit-pool span.
    pub fn template_parts(&self, span: TemplateSpan) -> &[TemplatePart] {
        &self.pools.template_parts[span.start as usize..(span.start + span.len) as usize]
    }
    /// Append template quasis without an owning per-template vector.
    pub fn template_info(&mut self, parts: &[TemplatePart], tagged: bool) -> JsId {
        let span = TemplateSpan { start: index(self.pools.template_parts.len()), len: index(parts.len()) };
        self.pools.template_parts.extend_from_slice(parts);
        self.js_info(if tagged { JsPayload::Tagged(span) } else { JsPayload::Template(span) })
    }
    /// O(1): borrow a property-key run without copying metadata.
    pub fn property_keys(&self, span: PropertySpan) -> &[PropertyKey] {
        &self.pools.property_keys[span.start as usize..(span.start + span.len) as usize]
    }
    /// O(keys.len()): append object keys to the unit pool, not a per-object vector.
    pub fn object_info(&mut self, keys: &[PropertyKey]) -> JsId {
        let span = PropertySpan {
            start: index(self.pools.property_keys.len()),
            len: index(keys.len()),
        };
        self.pools.property_keys.extend_from_slice(keys);
        self.js_info(JsPayload::Object(span))
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
        let id = FuncId(index(self.vars.funcs.len()));
        let attr_id = index(self.pools.attrs.len());
        self.pools.attrs.push(attr);
        self.func_owners.push(None);
        self.vars.funcs.push(FuncHeader {
            params,
            attr: attr_id,
            loc,
            flags: 0,
        });
        id
    }
    /// Allocate a fresh ordinary header while sharing immutable attributes.
    pub(crate) fn function_header_from(&mut self, source: FuncId, params: VarSpan) -> FuncId {
        let old = *self.function(source);
        let id = FuncId(index(self.vars.funcs.len()));
        self.func_owners.push(None);
        self.vars.funcs.push(FuncHeader { params, attr: old.attr, loc: old.loc, flags: 0 });
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
        self.vars.funcs[id.index()].flags |= FuncHeader::METHOD;
        id
    }
    /// Read a function header.
    pub fn function(&self, id: FuncId) -> &FuncHeader {
        &self.vars.funcs[id.index()]
    }
    /// O(1): read a parameter, including a lowered loop's noncontiguous copies.
    pub fn function_parameter(&self, id: FuncId, index: usize) -> VarId {
        self.vars.parameter(id, index)
    }
    /// Read a function's cold attributes.
    pub fn function_attributes(&self, id: FuncId) -> &FunctionAttribute {
        &self.pools.attrs[self.function(id).attr as usize]
    }
    /// O(keys + clauses): transfer import metadata into the unit's flat pools.
    pub fn switch_header(&mut self, header: SwitchInput) -> SwitchId {
        let keys = KeySpan {
            start: index(self.pools.switch_keys.len()),
            len: index(header.keys.len()),
        };
        let clauses = ClauseSpan {
            start: index(self.pools.switch_clauses.len()),
            len: index(header.clauses.len()),
        };
        self.pools.switch_keys.extend(header.keys);
        self.pools.switch_clauses.extend(header.clauses);
        self.switch_record(SwitchRecord {
            keys,
            clauses,
            constants: header.constants,
            consts_full: header.consts_full,
            blocks_full: header.blocks_full,
            has_default: header.has_default,
            dispatch: header.dispatch,
        })
    }
    /// O(1) amortized: store a header whose keys and clauses are already pooled.
    pub(in crate::bir) fn switch_record(&mut self, header: SwitchRecord) -> SwitchId {
        assert!(header.constants <= header.keys.len);
        let id = SwitchId(index(self.pools.switches.len()));
        self.pools.switches.push(header);
        id
    }
    /// O(1): borrow the two pooled runs and the dispatch facts.
    pub fn switch(&self, id: SwitchId) -> SwitchHeader<'_> {
        let h = &self.pools.switches[id.index()];
        SwitchHeader {
            keys: &self.pools.switch_keys
                [h.keys.start as usize..(h.keys.start + h.keys.len) as usize],
            clauses: &self.pools.switch_clauses
                [h.clauses.start as usize..(h.clauses.start + h.clauses.len) as usize],
            constants: h.constants,
            consts_full: h.consts_full,
            blocks_full: h.blocks_full,
            has_default: h.has_default,
            dispatch: &h.dispatch,
        }
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
    /// Intern an immutable block shape once per distinct unit metadata key.
    /// Source primitives are temporarily borrowed outside the arena during
    /// lowering, so output shapes cannot borrow that movable primitive vector.
    pub(crate) fn block_info(&mut self, tag: &crate::lambda::TagInfo) -> JsId {
        let mut key = std::mem::take(&mut self.pools.block_key_scratch);
        crate::binser::to_vec_reuse(tag, &mut key).expect("block shape encoding");
        let hash = self.pools.hash_builder.hash_one(&key);
        let info = if let Some(&(_, info, _, _)) = self.pools.block_index.find(hash, |&(_, _, start, len)| {
            self.pools.block_key_bytes[start as usize..(start + len) as usize] == key
        }) {
            info
        } else {
            let info = self.js_info(JsPayload::Block(tag.clone()));
            let start = index(self.pools.block_key_bytes.len());
            self.pools.block_key_bytes.extend_from_slice(&key);
            self.pools.block_index.insert_unique(hash, (hash, info, start, index(key.len())), |entry| entry.0);
            info
        };
        key.clear();
        self.pools.block_key_scratch = key;
        info
    }
    /// Append immutable record-rest metadata without an owning per-node vector.
    pub fn rest_info(&mut self, fields: impl IntoIterator<Item = RestField>) -> JsId {
        let start = index(self.pools.rest_fields.len());
        self.pools.rest_fields.extend(fields);
        let len = index(self.pools.rest_fields.len()) - start;
        self.js_info(JsPayload::Rest(RestSpan { start, len }))
    }
    /// Borrow a record-rest descriptor's fields.
    pub fn rest_fields(&self, span: RestSpan) -> &[RestField] {
        &self.pools.rest_fields[span.start as usize..(span.start + span.len) as usize]
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
