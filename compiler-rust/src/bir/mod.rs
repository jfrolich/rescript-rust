//! Dormant backend IR: packed mutable trees with module-local typed pools.
//!
//! Constructors consume detached roots. A finished unit has one root; temporary
//! forests are permitted while building an edit. `validate` checks a finished
//! tree, including all allocated slots. Handles belong to one arena and become
//! invalid when released (slots are reused). No compiler pipeline uses this IR.
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
}
impl Bir {
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
        if let Some(i) = self
            .pools
            .strings
            .iter()
            .position(|&(s, n)| &self.pools.text[s as usize..(s + n) as usize] == text)
        {
            return StrId(index(i));
        }
        let id = StrId(index(self.pools.strings.len()));
        self.pools
            .strings
            .push((index(self.pools.text.len()), index(text.len())));
        self.pools.text.push_str(text);
        id
    }
    /// Borrow interned text.
    pub fn text(&self, id: StrId) -> &str {
        let (start, len) = self.pools.strings[id.index()];
        &self.pools.text[start as usize..(start + len) as usize]
    }
    /// Intern a constant. Compound fields must already exist.
    pub fn intern_const(&mut self, value: Constant) -> ConstId {
        if let Some(i) = self.pools.consts.iter().position(|v| v == &value) {
            return ConstId(index(i));
        }
        let id = ConstId(index(self.pools.consts.len()));
        self.pools.consts.push(value);
        id
    }
    /// Store flat compound-constant fields.
    pub fn const_fields(&mut self, values: &[ConstId]) -> ConstSpan {
        for v in values {
            assert!(v.index() < self.pools.consts.len());
        }
        if values.is_empty() {
            return ConstSpan { start: 0, len: 0 };
        }
        if let Some(start) = self
            .pools
            .const_fields
            .windows(values.len())
            .position(|items| items == values)
        {
            return ConstSpan {
                start: index(start),
                len: index(values.len()),
            };
        }
        let span = ConstSpan {
            start: index(self.pools.const_fields.len()),
            len: index(values.len()),
        };
        self.pools.const_fields.extend_from_slice(values);
        span
    }
    /// Read a constant.
    pub fn constant(&self, id: ConstId) -> &Constant {
        &self.pools.consts[id.index()]
    }
    /// Intern a primitive and its location.
    pub fn intern_prim(&mut self, payload: PrimPayload) -> PrimId {
        if let Some(i) = self.pools.prims.iter().position(|p| p == &payload) {
            return PrimId(index(i));
        }
        let id = PrimId(index(self.pools.prims.len()));
        self.pools.prims.push(payload);
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
            !self.pools.catches.iter().any(|h| h.label == label),
            "duplicate static label"
        );
        let id = CatchId(index(self.pools.catches.len()));
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
        if let Some(i) = self.pools.imports.iter().position(|m| m == &module) {
            return ImportId(index(i));
        }
        let id = ImportId(index(self.pools.imports.len()));
        self.pools.imports.push(module);
        id
    }
}
