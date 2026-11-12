//! Typed pools. Node lists and text are append-only; nodes themselves are reusable.
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::{ApInfo, FunctionAttribute, LamLoc, SwitchDispatch};
use crate::name::Name;

macro_rules! handles {
    ($($name:ident),*) => {$ (
        #[doc = concat!("A module-local `", stringify!($name), "` pool index.")]
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize)]
        #[repr(transparent)]
        pub struct $name(pub(super) u32);
        impl $name {
            /// Numeric index for side tables; not a globally unique identity.
            pub fn index(self) -> usize { self.0 as usize }
        }
    )*};
}
handles!(
    NodeId, ListId, VarId, ConstId, PrimId, FuncId, SwitchId, ColdId, StrId, ApplyId, CatchId,
    ImportId, JsId
);

pub(super) fn index(n: usize) -> u32 {
    u32::try_from(n).expect("Bir pool exceeds u32 capacity")
}

/// A contiguous run of variables.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[repr(C)]
pub struct VarSpan {
    pub(super) start: u32,
    pub(super) len: u32,
}
impl VarSpan {
    /// Variables in declaration order.
    pub fn iter(self) -> impl Iterator<Item = VarId> {
        (self.start..self.start + self.len).map(VarId)
    }
    /// Number of variables.
    pub fn len(self) -> usize {
        self.len as usize
    }
    /// Whether the run is empty.
    pub fn is_empty(self) -> bool {
        self.len == 0
    }
}

#[derive(Default)]
pub(super) struct Lists(Vec<NodeId>);
impl Lists {
    pub(super) fn push(&mut self, items: &[NodeId]) -> ListId {
        let id = ListId(index(self.0.len()));
        self.0.push(NodeId(index(items.len())));
        self.0.extend_from_slice(items);
        id
    }
    /// Consume a statement-stack run directly, without an intermediate vector.
    pub(super) fn push_iter(&mut self, len: usize, items: impl Iterator<Item = NodeId>) -> ListId {
        let id = ListId(index(self.0.len()));
        self.0.push(NodeId(index(len)));
        self.0.extend(items);
        assert_eq!(self.0.len(), id.index() + 1 + len);
        id
    }
    pub(super) fn get(&self, id: ListId) -> &[NodeId] {
        let start = id.index();
        &self.0[start + 1..start + 1 + self.0[start].index()]
    }
}

/// Flat constant payload: compound constants reference earlier constants.
#[derive(Debug, Clone, serde::Serialize)]
pub enum Constant {
    /// Null.
    Null,
    /// Undefined, with unit representation marker.
    Undefined(bool),
    /// Boolean.
    Bool(bool),
    /// Signed machine-independent integer.
    Int(i64),
    /// Native integer (distinct from an ordinary integer in the source IR).
    NativeInt(i64),
    /// Nominal constructor with its complete runtime tag metadata.
    Constructor(crate::types::VariantTag),
    /// Integer with the existing compiler's optional pointer decoration.
    DecoratedInt {
        /// Signed value.
        value: i64,
        /// Native-width rather than ordinary integer.
        native: bool,
        /// Constructor/shape decoration.
        comment: crate::lambda::lam_constant::PointerInfo,
    },
    /// Character code point.
    Char(u32),
    /// Source spelling and its once-parsed IEEE-754 value.
    Float(FloatConstant),
    /// Big integer spelling, including sign.
    BigInt(StrId),
    /// Decoded bytes encoded using the compiler's string convention.
    String(StrId),
    /// Immutable string marker retained until lowering.
    ImmString(StrId),
    /// Pointer/constructor name.
    Pointer(StrId),
    /// Compound constant; fields live in the constant list pool.
    Block {
        /// Runtime block tag.
        tag: crate::lambda::lam_tag_info::TagInfo,
        /// Constant fields.
        fields: ConstSpan,
    },
    /// Optional constant.
    Some(ConstId),
    /// Module alias marker.
    ModuleAlias,
}
/// A float is identified by its interned spelling, not its bits: `1.` and
/// `1.00` occupy different constant entries. Future folding must compare values,
/// while printing uses spelling. Folded results must use the legacy folder's
/// spelling rules, not the spelling of an arbitrary equal operand. Today
/// `LamArena::fold_prim` and `raw_lambda/lower.rs` only produce integer or
/// boolean results from floats, not folded float arithmetic. For numeric
/// rendering, see `ocaml_float::js_number_to_string` (12/15/18 digit rule).
#[derive(Debug, Clone, serde::Serialize)]
pub struct FloatConstant {
    pub(super) spelling: StrId,
    pub(super) bits: u64,
}
impl FloatConstant {
    /// Parsed value, without parsing or a hash lookup.
    pub fn value(&self) -> f64 {
        f64::from_bits(self.bits)
    }
    /// Original spelling.
    pub fn spelling(&self) -> StrId {
        self.spelling
    }
}
/// Range in the constant-field pool.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
pub struct ConstSpan {
    pub(super) start: u32,
    pub(super) len: u32,
}

/// Primitive identity and source location, interned together.
#[derive(Debug, Clone, serde::Serialize)]
pub struct PrimPayload {
    /// Operation with its existing compiler metadata.
    pub primitive: Primitive,
    /// Source location.
    pub loc: LamLoc,
}
// Legacy primitive/tag payloads implement Serialize, but not Hash/Eq. Their
// compiler-owned binary encoding is a canonical key, including bitwise IEEE
// float encoding (unlike JSON and ordinary float equality). Cache these bytes
// once at interning; no changes to the legacy metadata types are necessary.
macro_rules! payload_key {
    ($ty:ty) => {
        impl $ty {
            pub(super) fn key(&self) -> Vec<u8> {
                crate::binser::to_vec(self).expect("Bir payload serialization")
            }
        }
        impl PartialEq for $ty {
            fn eq(&self, other: &Self) -> bool {
                self.key() == other.key()
            }
        }
        impl Eq for $ty {}
        impl std::hash::Hash for $ty {
            fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
                std::hash::Hash::hash(&self.key(), state);
            }
        }
    };
}
payload_key!(Constant);
payload_key!(PrimPayload);

/// Compact function header. Attributes are in a separate cold pool.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct FuncHeader {
    /// Parameter run.
    pub params: VarSpan,
    /// Source location.
    pub loc: LamLoc,
    pub(super) attr: u32,
    /// Function properties.
    pub flags: u32,
}
impl FuncHeader {
    /// Print as a method-capable function, preserving `this`.
    pub const METHOD: u32 = 2;
}
/// Static exception handler metadata.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct CatchHeader {
    /// Static exception label.
    pub label: u32,
    /// Handler parameters.
    pub params: VarSpan,
    pub(super) uses: u32,
}
impl CatchHeader {
    /// Weighted number of exits to this handler.
    pub fn uses(self) -> u32 {
        self.uses
    }
}
/// A switch case key at either abstraction level.
#[derive(Debug, Clone)]
pub enum CaseKey {
    /// Language-level integer or tagged/untagged constructor case.
    Lambda(crate::lambda::SwitchKey),
    /// String switch case.
    String(StrId),
    /// Lowered JavaScript literal case.
    JavaScript(crate::lambda::SwitchCaseTag),
}
/// Metadata attached to a lowered case, without its statement children.
#[derive(Debug, Clone, Copy)]
pub struct ClauseMeta {
    /// A break is emitted after the case body.
    pub should_break: bool,
    /// Case-label comment.
    pub comment: Option<StrId>,
    /// Case-label source location, retaining an explicit NONE handle too.
    pub loc: Option<LamLoc>,
}
/// Switch keys in their action order. Default, if present, is the final action.
#[derive(Debug, Clone)]
pub struct SwitchHeader {
    /// Integer/constructor keys followed by block keys.
    pub keys: Vec<CaseKey>,
    /// Optional lowered per-case metadata, including a final default entry.
    pub clauses: Vec<ClauseMeta>,
    /// Number of constant keys (the rest are block keys).
    pub constants: u32,
    /// Constant constructors are exhaustive.
    pub consts_full: bool,
    /// Block constructors are exhaustive.
    pub blocks_full: bool,
    /// A default action follows the keyed actions.
    pub has_default: bool,
    /// Runtime dispatch representation.
    pub dispatch: SwitchDispatch,
}
/// Source metadata; the node-parallel index is allocated only on demand.
#[derive(Debug, Clone, Copy)]
pub struct Cold {
    /// Source location.
    pub loc: LamLoc,
    /// Comment text, if any.
    pub comment: Option<StrId>,
}
/// Object key representation, including the two distinct spread semantics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropertyKey {
    /// Literal property name.
    Literal(StrId),
    /// Well-known symbol key.
    Symbol,
    /// General spread, which may invoke getters.
    Spread,
    /// Plain record spread.
    RecordSpread,
}
/// Cold JSX shape. Values are ordered callee, tag, spread, props, children, key.
#[derive(Debug, Clone, Default)]
pub struct JsxHeader {
    /// A spread expression precedes named properties.
    pub spread: bool,
    /// Property keys in source order.
    pub props: Vec<PropertyKey>,
    /// Number of child expressions.
    pub children: u32,
    /// A final key expression is present.
    pub key: bool,
    /// Children form an array rather than a single value.
    pub multi: bool,
    /// This is a fragment.
    pub fragment: bool,
}
/// One template segment's raw and cooked text.
#[derive(Debug, Clone, Copy)]
pub struct TemplatePart {
    /// Original escaped spelling.
    pub raw: StrId,
    /// Decoded value; absent for an invalid escape in a tagged template.
    pub cooked: Option<StrId>,
}
/// A field excluded from record-rest destructuring.
#[derive(Debug, Clone, Copy)]
pub struct RestField {
    /// Source property name.
    pub name: StrId,
    /// Optional local bound to the removed field by SRest.
    pub binding: Option<VarId>,
}
/// JavaScript metadata without child ownership. All expressions stay in node lists.
#[derive(Debug, Clone)]
pub enum JsPayload {
    /// Call kind, arity and method/JSX markers.
    Call(crate::js_ir::CallInfo),
    /// One key per object value, including spreads.
    Object(Vec<PropertyKey>),
    /// Fixed runtime block shape.
    Block(crate::lambda::lam_tag_info::TagInfo),
    /// JSX positional shape.
    Jsx(JsxHeader),
    /// Untagged template quasis; one more than interpolations.
    Template(Vec<TemplatePart>),
    /// Tagged template raw/cooked quasis.
    Tagged(Vec<TemplatePart>),
    /// Fields excluded from a record-rest expression/destructuring.
    Rest(Vec<RestField>),
}
/// Imported module identity, retained in encounter order.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Import {
    /// Module name.
    pub name: Name,
    /// Import path.
    pub path: StrId,
}

#[derive(Default)]
pub(super) struct Pools {
    pub hash_builder: ahash::RandomState,
    pub text_index: hashbrown::HashTable<(u64, StrId)>,
    pub const_index: hashbrown::HashTable<(u64, ConstId)>,
    pub const_keys: Vec<Vec<u8>>,
    pub prim_index: hashbrown::HashTable<(u64, PrimId)>,
    pub prim_keys: Vec<Vec<u8>>,
    pub import_index: hashbrown::HashTable<(u64, ImportId)>,
    pub catch_labels: hashbrown::HashMap<u32, CatchId, ahash::RandomState>,
    pub next_label: u64,
    pub consts: Vec<Constant>,
    pub floats: Vec<Option<ConstId>>,
    pub const_fields: Vec<ConstId>,
    pub const_fields_index: hashbrown::HashTable<(u64, ConstSpan)>,
    pub prims: Vec<PrimPayload>,
    pub funcs: Vec<FuncHeader>,
    pub attrs: Vec<FunctionAttribute>,
    pub switches: Vec<SwitchHeader>,
    pub catches: Vec<CatchHeader>,
    pub apply: Vec<ApInfo>,
    pub js: Vec<JsPayload>,
    pub cold: Vec<Cold>,
    pub imports: Vec<Import>,
    // J imports retain the complete module identity, including dynamic/default
    // flags and ordered import attributes. Indexed by ImportId, like imports.
    pub j_modules: Vec<crate::js_ir::ModuleId>,
    pub text: String,
    pub strings: Vec<(u32, u32)>,
}
