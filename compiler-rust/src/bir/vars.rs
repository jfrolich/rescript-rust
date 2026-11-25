//! Variable identity, persistent conservative flags, and maintained binding facts.
use super::pools::*;
use crate::name::Name;

/// Whether a bound function is recursive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum RecFlag {
    /// Nonrecursive binding.
    No,
    /// Recursive binding group.
    Yes,
}
/// Nullable option representation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum BoxedNullable {
    /// Null is absent.
    Null,
    /// Undefined is absent.
    Undefined,
    /// Either is absent.
    Both,
}
/// Binding summary. Payloads are handles, never owned subtrees.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Fact {
    /// No known binding value.
    Unknown,
    /// Function or handler parameter.
    Param,
    /// Constant value.
    Const(ConstId),
    /// Immutable block.
    Block(NodeId),
    /// Mutable block.
    MutableBlock(NodeId),
    /// Function value; arity is read from its header.
    Function {
        /// Function node.
        node: NodeId,
        /// Recursion status.
        rec: RecFlag,
    },
    /// Some value.
    Optional(NodeId),
    /// Nullable conversion.
    NullableOptional(NodeId, BoxedNullable),
    /// Imported module.
    Module(u32),
    /// Variable alias.
    Alias(VarId),
}
/// Monotonic variable properties, except EXPORTED which follows the export list.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[repr(transparent)]
pub struct VarFlags(pub(super) u8);
impl VarFlags {
    /// Has been assigned.
    pub const ASSIGNED: u8 = 1;
    /// Referenced across a function/loop capture boundary.
    pub const CAPTURED: u8 = 2;
    /// Named by an export.
    pub const EXPORTED: u8 = 4;
    /// Function or handler parameter.
    pub const PARAM: u8 = 8;
    /// JavaScript global.
    pub const JS_GLOBAL: u8 = 16;
    /// Module identity.
    pub const MODULE: u8 = 32;
    /// Imported identity is a JavaScript identifier or a persistent global.
    pub const JS_IDENT: u8 = 64;
    /// Test a property.
    pub fn contains(self, bit: u8) -> bool {
        self.0 & bit != 0
    }
}
/// Structure-of-arrays storage; mutation is restricted to Bir's editing API.
#[derive(Default)]
pub struct VarTable {
    /// J-only copies retain their source printing identity while owning distinct binders.
    pub(super) j_origin: Vec<VarId>,
    pub(super) name: Vec<Name>,
    pub(super) order: Vec<u32>,
    pub(super) flags: Vec<VarFlags>,
    pub(super) uses: Vec<u32>,
    pub(super) binder: Vec<Option<NodeId>>,
    pub(super) fact: Vec<Fact>,
    pub(super) printed: Vec<Option<Name>>,
    /// Function headers, dense by FuncId. A header is a run of parameters,
    /// so it lives with the variables: the naming log reads a function's
    /// parameters through this table (`lower::names`).
    pub(super) funcs: Vec<FuncHeader>,
    /// The parameter runs of headers with `INDIRECT_PARAMS`.
    pub(super) function_params: Vec<VarId>,
}
impl VarTable {
    /// Number of variables, including released binders.
    pub fn len(&self) -> usize {
        self.name.len()
    }
    /// Whether the table is empty.
    pub fn is_empty(&self) -> bool {
        self.name.is_empty()
    }
    /// Source name.
    pub fn name(&self, v: VarId) -> Name {
        self.name[v.index()]
    }
    /// Creation order used for deterministic naming.
    pub fn order(&self, v: VarId) -> u32 {
        self.order[v.index()]
    }
    /// Current weighted uses.
    pub fn uses(&self, v: VarId) -> u32 {
        self.uses[v.index()]
    }
    /// Conservative properties.
    pub fn flags(&self, v: VarId) -> VarFlags {
        self.flags[v.index()]
    }
    /// Binding node, if live.
    pub fn binder(&self, v: VarId) -> Option<NodeId> {
        self.binder[v.index()]
    }
    /// Current binding summary.
    pub fn fact(&self, v: VarId) -> Fact {
        self.fact[v.index()]
    }
    /// The header of `f`. Constant.
    pub fn function(&self, f: FuncId) -> &FuncHeader {
        &self.funcs[f.index()]
    }
    /// Parameter `index` of `f`, including a lowered loop's noncontiguous
    /// copies. Constant.
    pub fn parameter(&self, f: FuncId, index: usize) -> VarId {
        let h = &self.funcs[f.index()];
        assert!(index < h.params.len());
        if h.flags & FuncHeader::INDIRECT_PARAMS != 0 {
            self.function_params[h.params.start as usize + index]
        } else {
            VarId(h.params.start + index as u32)
        }
    }
    /// The parameters of `f` in order. Constant per parameter.
    pub fn parameters(&self, f: FuncId) -> impl Iterator<Item = VarId> + '_ {
        (0..self.funcs[f.index()].params.len()).map(move |index| self.parameter(f, index))
    }
    /// The variable a J copy prints as (itself for an original). Constant.
    pub fn origin(&self, v: VarId) -> VarId {
        self.j_origin[v.index()]
    }
    /// Name assigned by a future naming pass.
    pub fn printed(&self, v: VarId) -> Option<Name> {
        self.printed[v.index()]
    }
}
