//! Immutable publication pools. Names and paths are indices, never owned per item.
use super::graph::{Node, Param, Ty};
use super::template::Template;

/// A namespace tag occupies one byte in an export row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum ExportKind {
    Value,
    Type,
    Constructor,
    Label,
    Module,
    ModuleType,
}

/// One name in an export table. Payload indexes the pool selected by kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct ExportItem {
    pub name: u32,
    pub payload: u32,
    pub kind: ExportKind,
}

/// A contiguous export-table range; the root table is child table zero.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct ChildTable {
    pub start: u32,
    pub len: u32,
}

/// The pool selected by a declaration's member range.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum DeclarationKind {
    Abstract,
    Record,
    Variant,
    Open,
}

/// Cold type-declaration metadata; all references index segment pools.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct TypeDecl {
    pub kind: DeclarationKind,
    /// Bits: private, immediate, unboxed, local constraint, abbreviation.
    pub flags: u8,
    pub arity: u16,
    pub params: u32,
    pub manifest: u32,
    pub members: u32,
    pub member_len: u32,
    pub path: u32,
    pub loc: u32,
    pub variance: u32,
}

/// Constructor or record-label metadata, kept out of the type-node array.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct MemberDecl {
    pub name: u32,
    pub args: u32,
    pub tag_or_pos: u32,
    pub flags: u32,
}

/// Published storage contains no graph context, cell, lock or borrowed data.
/// Each table's items are sorted by numeric interned name. Equal names in
/// different namespaces are adjacent; lookup returns any matching namespace.
#[derive(Default)]
pub struct Segment {
    pub nodes: Box<[Node]>,
    pub lists: Box<[Ty]>,
    pub params: Box<[Param]>,
    pub templates: Box<[Template]>,
    /// A variable's name is in the level field (tc/template.rs `descriptor`).
    pub(crate) template_nodes: Box<[Node]>,
    pub(crate) template_lists: Box<[Ty]>,
    pub(crate) template_params: Box<[Param]>,
    pub(crate) template_pools: Box<[super::template::TemplatePools]>,
    pub(crate) template_externals: Box<[Ty]>,
    /// Publication identity of each template node, in the combined shared /
    /// template numbering. Instantiation still copies each item's template;
    /// printing and inverse conversion use these identities to preserve aliases
    /// that cross a non-generic boundary. Empty means each stored node is unique.
    pub(crate) template_origins: Box<[Ty]>,
    pub type_declarations: Box<[TypeDecl]>,
    pub members: Box<[MemberDecl]>,
    pub items: Box<[ExportItem]>,
    pub children: Box<[ChildTable]>,
    pub digest: [u8; 32],
    pub signature: SignaturePools,
}

impl Segment {
    /// O(1): source identity, without changing the instantiation representation.
    pub(crate) fn publication_node(&self, node: u32) -> u32 {
        let shared = self.nodes.len() as u32;
        if node < shared || self.template_origins.is_empty() {
            node
        } else {
            self.template_origins[(node - shared) as usize].0
        }
    }

    /// O(log n) probes, O(1) stack and no allocation, for n root exports.
    /// Returns None for an empty segment. Names use the publisher's interner.
    pub fn lookup(&self, name: u32) -> Option<&ExportItem> {
        self.children
            .first()
            .and_then(|&table| self.lookup_in(table, name))
    }

    /// O(log n) probes, at most floor(log2(n)) + 1 for a nonempty table.
    /// The caller supplies a valid table range; invalid ranges panic.
    pub fn lookup_in(&self, table: ChildTable, name: u32) -> Option<&ExportItem> {
        let start = table.start as usize;
        let items = &self.items[start..start + table.len as usize];
        let mut lo = 0;
        let mut hi = items.len();
        while lo < hi {
            #[cfg(test)]
            super::steps::tick();
            let mid = lo + (hi - lo) / 2;
            match items[mid].name.cmp(&name) {
                std::cmp::Ordering::Less => lo = mid + 1,
                std::cmp::Ordering::Greater => hi = mid,
                std::cmp::Ordering::Equal => return Some(&items[mid]),
            }
        }
        None
    }
}

/// O(1), compile-time trait assertion; no runtime work.
const fn assert_send_sync<T: Send + Sync>() {}
const _: () = assert_send_sync::<Segment>();

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::steps;

    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<ExportKind>(), 1);
        assert_eq!(std::mem::size_of::<ExportItem>(), 12);
        assert_eq!(std::mem::size_of::<ChildTable>(), 8);
        assert_eq!(std::mem::size_of::<TypeDecl>(), 32);
        assert_eq!(std::mem::size_of::<MemberDecl>(), 16);
        assert_eq!(std::mem::size_of::<Segment>(), 1032);
    }

    #[test]
    fn ten_thousand_names_need_at_most_fifteen_probes() {
        let segment = Segment {
            items: (0..10000)
                .map(|i| ExportItem {
                    name: i * 2,
                    payload: i,
                    kind: ExportKind::Value,
                })
                .collect(),
            children: Box::new([ChildTable {
                start: 0,
                len: 10000,
            }]),
            ..Segment::default()
        };
        for name in 0..=20000 {
            let probes = steps::scope(|| {
                let found = segment.lookup(name);
                assert_eq!(
                    found.map(|item| item.payload),
                    (name < 20000 && name % 2 == 0).then_some(name / 2)
                );
            });
            assert!(probes <= 15, "{name}: {probes} probes");
        }
        assert!(segment.lookup(u32::MAX).is_none());
    }

    #[test]
    fn child_tables_are_independent_and_empty_tables_are_valid() {
        let segment = Segment {
            items: Box::new([
                ExportItem {
                    name: 7,
                    payload: 0,
                    kind: ExportKind::Module,
                },
                ExportItem {
                    name: 7,
                    payload: 1,
                    kind: ExportKind::Value,
                },
            ]),
            children: Box::new([
                ChildTable { start: 0, len: 1 },
                ChildTable { start: 1, len: 1 },
                ChildTable { start: 2, len: 0 },
            ]),
            ..Segment::default()
        };
        assert_eq!(segment.lookup(7).unwrap().kind, ExportKind::Module);
        assert_eq!(
            segment.lookup_in(segment.children[1], 7).unwrap().payload,
            1
        );
        assert!(segment.lookup_in(segment.children[2], 7).is_none());
        assert!(Segment::default().lookup(7).is_none());
    }
}

/// A range in the pool named by its containing field. Empty ranges allocate
/// nothing. Optional pool indices use graph::NONE, never an empty range.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct Range {
    pub start: u32,
    pub len: u32,
}

// All declaration data is cold, owned once by the segment. These rows are not
// values passed down the type walk. References are indices, including strings.
macro_rules! row {
    ($(#[$meta:meta])* $name:ident, $size:expr, {$($(#[$doc:meta])* $field:ident: $ty:ty),* $(,)?}) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        #[repr(C)]
        pub struct $name { $($(#[$doc])* pub $field: $ty),* }
        const _: () = assert!(std::mem::size_of::<$name>() == $size);
    };
}

row!(PositionRow, 16, { filename: u32, line: i32, beginning_of_line: i32, offset: i32 });
row!(LocationRow, 40, {
    start: PositionRow, end: PositionRow,
    /// `Location::origin`: the declaration identity of a coordinate-free location.
    origin: u32, ghost: bool,
});

row!(UnitRow, 16, {
    name: u32, deprecated: u32, signature: u32, path: u32,
});
row!(IdentRow, 16, {
    name: u32, stamp: i32, flags: u32,
    /// Absolute enclosing scope; distinct functor binders remain distinct.
    /// An item binder (and every identifier naming it) holds the binder's
    /// `ordered_items` index; a functor parameter `FUNCTOR_SCOPE | ` its
    /// functor's `module_types` index; the unit itself `UNIT_SCOPE`; an
    /// identifier bound outside the signature graph::NONE.
    scope: u32,
});
/// `IdentRow::scope` of the persistent identifier naming the unit itself.
pub const UNIT_SCOPE: u32 = u32::MAX - 1;
/// `IdentRow::scope` flag of a functor parameter.
pub const FUNCTOR_SCOPE: u32 = 1 << 31;
/// `ExportItem::payload` flag of a constructor that is an `extensions` row
/// rather than a `members` row.
pub const EXTENSION_PAYLOAD: u32 = 1 << 31;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PathRow {
    Ident(u32),
    Dot {
        parent: u32,
        name: u32,
        position: i32,
    },
    Apply {
        functor: u32,
        argument: u32,
    },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LongidentRow {
    Ident(u32),
    Dot { parent: u32, name: u32 },
    Apply { functor: u32, argument: u32 },
    /// Unresolved component's raw diagnostic index (not a graph reference).
    Unresolved(u32),
    UnresolvedDot { parent: u32, raw: u32 },
}

/// Unlike the sorted lookup index, signature rows retain declaration order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SignatureKind {
    Value,
    Type,
    Extension,
    Module,
    ModuleType,
    Class,
    ClassType,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RecStatus {
    Not,
    First,
    Next,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExtensionStatus {
    First,
    Next,
    Exception,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ItemStatus {
    Ordinary,
    Recursive(RecStatus),
    Extension(ExtensionStatus),
}
row!(SignatureItemRow, 12, {
    ident: u32, declaration: u32, kind: SignatureKind, status: ItemStatus,
});
row!(ValueRow, 24, {
    ty: u32, primitive: u32, attributes: Range, loc: u32,
    /// Original path, or an absolute (unit, item) binder address.
    path: u32,
});
row!(
    /// A module declaration, or (for a `SignatureKind::ModuleType` item) a module
    /// type declaration, whose module type is NONE when abstract. Its path is
    /// original or an absolute (unit, item) binder address.
    ModuleRow, 20, { module_type: u32, attributes: Range, loc: u32, path: u32 }
);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModuleTypeRow {
    Ident(u32),
    Alias {
        path: u32,
        present: bool,
    },
    Signature(u32),
    Functor {
        parameter: u32,
        parameter_type: u32,
        result: u32,
    },
}

row!(TypeDetailsRow, 48, {
    parameter_roots: Range, variance: Range, attributes: Range,
    inlined_records: Range, representation: u32, shape: u32,
    /// Optional local abstract-type level pair, retained for tooling.
    newtype_level: u32, scope_level: u32,
});
row!(InlinedRecordRow, 12, { name: u32, labels: Range });
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RecordRepresentationRow {
    Regular,
    Array,
    Unboxed(bool),
    Extension,
    Inlined {
        name: u32,
        position: u32,
        layout: u32,
    },
}
row!(LabelRow, 28, {
    ident: u32, runtime_name: u32, ty: u32, attributes: Range,
    loc: u32, mutable: bool, optional: bool,
});
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstructorArgumentsRow {
    Tuple(Range),
    Record(Range),
}
row!(ConstructorRow, 28, {
    ident: u32, runtime_tag: u32, arguments: u32, result: u32,
    attributes: Range, loc: u32,
});
row!(ExtensionRow, 36, {
    path: u32, parameters: Range, result: u32, arguments: u32,
    attributes: Range, loc: u32, private: bool, exception: bool,
});

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlockTypeRow {
    Number,
    String,
    Bigint,
    Boolean,
    Array,
    Symbol,
    Function,
    Object,
    Unknown,
    Class { name: u32, ancestors: Range },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShapeRow {
    Unstated,
    NeverUndefined,
    Recognized(u32),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LiteralRow {
    String(u32),
    Int(i64),
    Float(u32),
    BigInt(u32),
    Bool(bool),
    Null,
    Undefined,
}
row!(LayoutRow, 16, { constructors: Range, tag_name: u32, unboxed: bool });
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuntimeConstructorRow {
    Constant {
        name: u32,
        literal: u32,
    },
    Tagged {
        name: u32,
        literal: u32,
        tag_name: u32,
    },
    Untagged {
        name: u32,
        literal: u32,
        block_type: u32,
    },
}

row!(AttributeRow, 16, { name: u32, payload: u32, name_loc: u32, loc: u32 });
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AttributePayloadRow {
    Empty,
    Str(u32),
    Int(i64),
    IntLiteral(u32),
    Float(u32),
    BigInt(u32),
    Bool(bool),
    Ident(u32),
    Deprecated(u32),
    Structure(Range),
    SemanticString(u32),
    StrTuple(Range),
}
/// Err holds a location; Missing is distinct from the empty string.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SemanticStringValue {
    Missing,
    Valid(u32),
    Invalid(u32),
}
row!(SemanticStringRow, 16, {
    value: SemanticStringValue, braces: u32, template: bool,
});
row!(DeprecatedRow, 20, {
    reason: SemanticStringValue, migrate: u32, migrate_in_pipe_chain: u32,
    can_be_automigrated: bool,
});
row!(StringPair, 8, { first: u32, second: u32 });
row!(StringIntPair, 16, { name: u32, value: i64 });
row!(MarshalFragmentRow, 20, { bytes: Range, objects: u32, size_32: u32, size_64: u32 });

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrimitiveKindRow {
    Intrinsic,
    External(u32),
    Inline(u32),
}
row!(PrimitiveRow, 20, {
    name: u32, arity: i32, kind: PrimitiveKindRow,
    native_float: bool, from_constructor: bool,
});
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstantArgumentRow {
    Int(i64),
    String(u32),
    Json(u32),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FfiAttributeRow {
    PolyVarString(Range),
    /// NONE means absent, otherwise indexes a range in the ranges pool.
    PolyVar(u32),
    Int(Range),
    Constant(u32),
    Unit,
    Nothing,
    Ignore,
    Unwrap,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FfiLabelRow {
    Positional,
    Labelled,
    Optional,
    ObjectEmpty,
    ObjectLabel(u32),
    ObjectOptional { name: u32, no_nested_option: bool },
}
row!(FfiParamRow, 12, { attribute: u32, label: FfiLabelRow });
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReturnWrapperRow {
    Unset,
    Identity,
    NullToOption,
    NullUndefinedToOption,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FfiRow {
    Call {
        params: Range,
        declaration: u32,
        return_wrapper: ReturnWrapperRow,
    },
    Object(Range),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExternalKindRow {
    Value(u32),
    Send(u32),
    New(u32),
    Get(u32),
    Set(u32),
    GetIndex,
    SetIndex,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ModuleSourceRow {
    Absent,
    Itself,
    Named(u32),
}
row!(ExternalDeclRow, 40, {
    kind: ExternalKindRow, module: ModuleSourceRow, scopes: Range,
    effective_arity: i64, variadic: bool,
});
row!(ExternalModuleRow, 12, {
    bundle: u32, binding_hint: u32,
    /// Optional range of ordered import attribute pairs.
    import_attributes: u32,
});
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InlineConstantRow {
    String(u32),
    Bool(bool),
    Int(i32),
    Bigint { positive: bool, digits: u32 },
    Float(u32),
}

// Cold payloads for descriptors outside the four R1 kernel descriptor shapes.
//
// Such a node is `TUPLE | EXTENDED | arity << 8`: `tag()` stays TUPLE and its
// children (every type it refers to) live in the graph's ordinary list pool at
// `b`, so R1's capture, copy and instance relocate them without knowing the
// descriptor. `a` indexes `SignaturePools::descriptor_extras`, which is never
// rewritten by those operations: payloads name children by their position in
// the node's own list (a "slot"), never by a graph handle. Slot ranges are
// relative to the node's list start. The occurrence's level and physical
// identity stay in the node.

/// Head flag of an extended descriptor; bit 4 is outside the tag nibble.
pub const EXTENDED: u32 = 1 << 4;

/// Descriptor payload of an `EXTENDED` node, with its children's slot layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExtraDescriptor {
    /// `Tobject`: slot 0 is the field list.
    Object,
    /// `Tfield`: slot 0 the field's type, slot 1 the rest of the list. The name
    /// is a string; mutability indexes `SignaturePools::mutabilities`, keeping
    /// shared cells shared and distinct equal-valued cells distinct.
    Field { name: u32, mutability: u32 },
    /// `Tnil`: no children.
    Nil,
    /// `Tunivar` with its optional name (NONE), no children.
    Univar(u32),
    /// `Tpoly`: slot 0 the body, slots 1.. the bound variables.
    Poly,
    /// `Tvariant`: the `variants` row; its slots are listed there.
    Variant(u32),
    /// `Tpackage`: the `packages` row; every slot is a package argument.
    Package(u32),
    /// `Tsubst`: slot 0 the target.
    Substitution,
}
row!(
    /// A root within one item's template. Multiple declaration fields use roots
    /// of the same template, preserving sharing across those fields. `ty` is
    /// a template reference: with bit 30 set, a node relative to the first
    /// node of an instance of `template`; otherwise an absolute node of the
    /// segment (a non-generic root, shared across items).
    SchemeRoot, 8, { template: u32, ty: Ty }
);

row!(
    /// A row: `fields` index `row_fields`; `more` is a slot and
    /// `name_arguments` a slot range of the owning node; `name` a path or NONE.
    VariantRow, 28, {
    fields: Range, more: u32, name: u32, name_arguments: Range,
    closed: bool, fixed: bool,
});
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RowFieldKind {
    Present,
    Absent,
    Either { constant: bool, matched: bool },
}
row!(
    /// `types` is a slot range of the owning node (one slot for a present
    /// field with an argument). `link` is NONE: a frozen row has no links.
    RowFieldRow, 20, { name: u32, types: Range, link: u32, kind: RowFieldKind }
);
row!(
    /// `longidents` indexes `indices`, each a `longidents` row; `arguments` is
    /// the owning node's slot range.
    PackageRow, 20, { path: u32, longidents: Range, arguments: Range }
);

/// All cold signature metadata. Type nodes and templates remain in Segment's
/// hot pools. Ranges select boxed slices; no row owns a string, Vec or pointer.
#[derive(Default)]
pub struct SignaturePools {
    pub unit: Option<UnitRow>,
    pub bytes: Box<[u8]>,
    pub strings: Box<[Range]>,
    pub ranges: Box<[Range]>,
    pub indices: Box<[u32]>,
    pub identifiers: Box<[IdentRow]>,
    pub paths: Box<[PathRow]>,
    pub longidents: Box<[LongidentRow]>,
    pub ordered_items: Box<[SignatureItemRow]>,
    pub signatures: Box<[Range]>,
    pub values: Box<[ValueRow]>,
    pub modules: Box<[ModuleRow]>,
    pub module_types: Box<[ModuleTypeRow]>,
    pub type_details: Box<[TypeDetailsRow]>,
    pub inlined_records: Box<[InlinedRecordRow]>,
    pub record_representations: Box<[RecordRepresentationRow]>,
    pub labels: Box<[LabelRow]>,
    pub constructor_arguments: Box<[ConstructorArgumentsRow]>,
    pub constructors: Box<[ConstructorRow]>,
    pub extensions: Box<[ExtensionRow]>,
    pub block_types: Box<[BlockTypeRow]>,
    pub shapes: Box<[ShapeRow]>,
    pub literals: Box<[LiteralRow]>,
    pub layouts: Box<[LayoutRow]>,
    pub runtime_constructors: Box<[RuntimeConstructorRow]>,
    pub attributes: Box<[AttributeRow]>,
    pub attribute_payloads: Box<[AttributePayloadRow]>,
    pub semantic_strings: Box<[SemanticStringRow]>,
    pub deprecations: Box<[DeprecatedRow]>,
    pub string_pairs: Box<[StringPair]>,
    pub string_int_pairs: Box<[StringIntPair]>,
    pub marshal_fragments: Box<[MarshalFragmentRow]>,
    pub primitives: Box<[PrimitiveRow]>,
    pub constant_arguments: Box<[ConstantArgumentRow]>,
    pub ffi_attributes: Box<[FfiAttributeRow]>,
    pub ffi_params: Box<[FfiParamRow]>,
    pub ffi: Box<[FfiRow]>,
    pub external_declarations: Box<[ExternalDeclRow]>,
    pub external_modules: Box<[ExternalModuleRow]>,
    pub inline_constants: Box<[InlineConstantRow]>,
    pub variants: Box<[VariantRow]>,
    pub row_fields: Box<[RowFieldRow]>,
    pub packages: Box<[PackageRow]>,
    pub variance: Box<[u8]>,
    pub locations: Box<[LocationRow]>,
    pub descriptor_extras: Box<[ExtraDescriptor]>,
    /// Initial values of distinct persistent field cells, by identity.
    pub mutabilities: Box<[bool]>,
    pub roots: Box<[SchemeRoot]>,
}

#[cfg(test)]
mod schema_tests {
    use super::*;
    #[test]
    fn schema_rows_are_pinned() {
        macro_rules! sizes {
            ($($ty:ty => $n:expr),* $(,)?) => { $(assert_eq!(std::mem::size_of::<$ty>(), $n, stringify!($ty));)* };
        }
        sizes!(
            DeclarationKind => 1, PositionRow => 16, LocationRow => 40,
            SignaturePools => 776, ExtraDescriptor => 12, SchemeRoot => 8, Range => 8, UnitRow => 16, IdentRow => 16, PathRow => 16,
            LongidentRow => 12, SignatureKind => 1, RecStatus => 1,
            ExtensionStatus => 1, ItemStatus => 2, SignatureItemRow => 12,
            ValueRow => 24, ModuleRow => 20, ModuleTypeRow => 16,
            TypeDetailsRow => 48, InlinedRecordRow => 12, RecordRepresentationRow => 16,
            LabelRow => 28, ConstructorArgumentsRow => 12, ConstructorRow => 28,
            ExtensionRow => 36, BlockTypeRow => 16, ShapeRow => 8, LiteralRow => 16,
            LayoutRow => 16, RuntimeConstructorRow => 16, AttributeRow => 16,
            AttributePayloadRow => 16, SemanticStringValue => 8, SemanticStringRow => 16,
            DeprecatedRow => 20, StringPair => 8, StringIntPair => 16,
            MarshalFragmentRow => 20, PrimitiveKindRow => 8, PrimitiveRow => 20,
            ConstantArgumentRow => 16, FfiAttributeRow => 12, FfiLabelRow => 8,
            FfiParamRow => 12, ReturnWrapperRow => 1, FfiRow => 16,
            ExternalKindRow => 8, ModuleSourceRow => 8, ExternalDeclRow => 40,
            ExternalModuleRow => 12, InlineConstantRow => 8,
            VariantRow => 28, RowFieldKind => 2, RowFieldRow => 20, PackageRow => 20,
        );
    }
}
