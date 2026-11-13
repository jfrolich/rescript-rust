//! The plan of a derived item: what the seam hands the checker and the
//! backend instead of syntax (`compiler-rust/docs/DERIVED_CODECS.md`, "Target
//! design").
//!
//! A plan is generic. It names the bindings an item declares and, per
//! binding, the ordered obligations the checker discharges, the type the
//! binding gets and a body in a small core language that the backend lowers.
//! Nothing here names a derive.
//!
//! Everything lives in dense pools of the `ParseArena`, addressed by `u32`
//! handles. A binding owns a contiguous range of obligations, of skeleton
//! nodes and of body nodes, so reading a plan is a forward scan of each pool.

use serde::{Deserialize, Serialize};

use crate::parse_arena::{ExprIdx, LidentIdx, LocIdx, StrIdx};
use crate::parser::ast::Attributes;

macro_rules! handle {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
        pub struct $name(pub u32);

        impl $name {
            /// The pool slot this handle names. Cost: O(1).
            #[inline]
            pub fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

handle!(
    /// A derived structure item: `StructureItemDesc::Pstr_derived`.
    DerivedIdx
);
handle!(
    /// One binding a derived item declares.
    BindingIdx
);
handle!(
    /// One obligation. Obligation results are a dense table indexed by it.
    ObligationIdx
);
handle!(
    /// The first node of a type skeleton, stored in prefix order.
    SkeletonIdx
);
handle!(
    /// One node of a binding's body.
    BodyIdx
);
handle!(
    /// The first node of a case pattern, stored in prefix order.
    PatIdx
);

/// A half-open range of slots in one pool.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    /// First slot.
    pub start: u32,
    /// Number of slots.
    pub len: u32,
}

impl Span {
    /// The slots as indices. Cost: O(1).
    #[inline]
    pub fn range(self) -> std::ops::Range<usize> {
        self.start as usize..(self.start + self.len) as usize
    }
}

/// A derived item: its bindings. The syntax it stands for is not generated:
/// a unit whose plan cannot be used is compiled again with plans off.
#[derive(Debug, Clone, Copy)]
pub struct Item {
    /// The bindings, in declaration order.
    pub bindings: Span,
}

/// Where an obligation's expression is located, relative to its name. The
/// derive gives an identifier either the location of the type constructor it
/// was generated for, or none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExprLoc {
    /// The expression carries the location of its name.
    OfName,
    /// The expression carries the arena's dummy location.
    Dummy,
}

/// The type a constructor obligation states its constructor belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Owner {
    /// The predefined `option`.
    Option,
    /// The predefined `result`.
    Result,
    /// The type a `Type` obligation resolved.
    Type,
    /// The declaration being derived: an unqualified name whose first
    /// candidate in scope is an ordinary constructor, possibly of an inline
    /// record. The skeletons of a binding's declared constructors share their
    /// result variable, so they belong to one type.
    Declared,
}

/// Where the body uses a constructor, and the location its name carries
/// there.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Site {
    /// In an expression; the name carries the dummy location.
    Construct,
    /// In an expression; the name carries no location.
    ConstructNone,
    /// In a pattern; the name carries no location.
    Pattern,
    /// In a pattern; the name carries the dummy location.
    PatternDummy,
}

/// How the body uses a label, and the location its name carries there.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LabelUse {
    /// A field access; the name carries no location.
    Access,
    /// A field access; the name carries the dummy location.
    AccessDummy,
    /// A field of a record expression; the name carries no location. The
    /// labels of one record expression are consecutive obligations.
    Construct,
    /// A field of a closed record pattern of an inline record; the name
    /// carries no location. Found by the type of the record, which a
    /// preceding constructor obligation fixed; the labels of one pattern are
    /// consecutive obligations, all of the record's, in order.
    Pattern,
    /// A field of a record expression of an inline record; the name carries
    /// no location. Found as `Pattern` is.
    ConstructInline,
    /// The field a record update `{...base, label: value}` writes; the name
    /// carries the dummy location. Found by the type of the base.
    Update,
}

/// No variable slot: a `Type` obligation that annotates nothing.
pub const NO_VAR: u32 = u32::MAX;

/// What the checker must establish for one name the body uses. Obligations
/// of a binding are stored in the order inference meets the identifiers of
/// the general form, which fixes the first failure and the order of warnings.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Obligation {
    /// A value: looked up as an identifier expression is (usage marking and
    /// the deprecation check included), instantiated once, and the instance
    /// unified with the instantiated `skeleton`.
    Value {
        /// The name, resolved in the environment of the item.
        name: LidentIdx,
        /// Location of the name: where its warnings are reported.
        name_loc: LocIdx,
        /// The type the body uses the value at.
        skeleton: SkeletonIdx,
        /// Location of the identifier expression.
        expr_loc: ExprLoc,
        /// Whether the body calls the value: a deprecated value is recorded
        /// as called or as referenced.
        called: bool,
    },
    /// A type constructor: looked up as a type annotation is. Skeletons name
    /// it through `SkeletonNode::Named`.
    Type {
        /// The name, resolved in the environment of the item.
        name: LidentIdx,
        /// Location of the name.
        name_loc: LocIdx,
        /// The number of type arguments skeletons apply it to.
        arity: u16,
        /// The variable slot the type annotates (`(e: t)`), which is unified
        /// with the constructor applied to nothing, or [`NO_VAR`].
        var: u32,
    },
    /// A record label, found as a field access or a record expression finds
    /// it: instantiated once, its argument and result unified with the two
    /// skeletons at `skeleton` (the argument's, then the record's).
    Label {
        /// The label's name.
        name: LidentIdx,
        /// The argument's skeleton, followed by the record's.
        skeleton: SkeletonIdx,
        /// How the body uses the label.
        usage: LabelUse,
    },
    /// A constructor: looked up by name, it must be the one of `of`;
    /// instantiated once, its arguments and result unified with the
    /// skeletons at `skeleton`.
    Constructor {
        /// The constructor's name.
        name: LidentIdx,
        /// The skeletons of the `args` arguments, followed by the result's.
        skeleton: SkeletonIdx,
        /// The type the constructor must belong to.
        of: Owner,
        /// Where the body uses it.
        site: Site,
        /// The number of arguments the body gives it; a constructor of an
        /// inline record takes the record as its one argument.
        args: u16,
    },
    /// A constant of the user's source (`@spice.key("k")`,
    /// `@spice.default(0)`): its type is unified with the skeleton.
    Literal {
        /// The constant expression.
        expr: ExprIdx,
        /// The type the body uses it at.
        skeleton: SkeletonIdx,
    },
}

impl Obligation {
    /// The name the obligation resolves; a literal has none. Cost: O(1).
    #[inline]
    pub fn name(self) -> Option<LidentIdx> {
        match self {
            Obligation::Value { name, .. }
            | Obligation::Type { name, .. }
            | Obligation::Label { name, .. }
            | Obligation::Constructor { name, .. } => Some(name),
            Obligation::Literal { .. } => None,
        }
    }
}

/// One node of a type skeleton. A skeleton is stored in prefix order: a node
/// is followed by its children, so it has no child handles and instantiating
/// it is one forward scan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SkeletonNode {
    /// A type variable of the binding. Slots are shared by the skeletons of
    /// one binding: the first use makes the variable, later uses denote it.
    Var(u32),
    /// A function type: `params` parameter skeletons follow, then the result.
    Arrow {
        /// Number of unlabelled parameters.
        params: u16,
    },
    /// The constructor a `Type` obligation resolved, applied to `args`
    /// skeletons that follow.
    Named {
        /// The `Type` obligation; it precedes every skeleton that names it.
        ty: ObligationIdx,
        /// Number of type arguments.
        args: u16,
    },
    /// A tuple of the `len` skeletons that follow.
    Tuple {
        /// Number of components.
        len: u16,
    },
    /// A predefined type constructor applied to the `args` skeletons that
    /// follow.
    Predef {
        /// The constructor.
        ty: Predef,
        /// Number of type arguments.
        args: u8,
    },
    /// Inside an `Arrow`, before a parameter's skeleton: the parameter is
    /// optional and labelled, and the skeleton that follows is the type of
    /// the value it holds when supplied.
    Optional(StrIdx),
}

/// The predefined types a skeleton names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Predef {
    /// `string`.
    String,
    /// `option<'a>`.
    Option,
    /// `array<'a>`.
    Array,
    /// `result<'a, 'b>`.
    Result,
    /// `int`.
    Int,
    /// `bool`.
    Bool,
}

/// The optional first argument of an application.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptionalArg {
    /// The callee is applied to unlabelled arguments only.
    Absent,
    /// The callee's first parameter is optional and the application leaves
    /// it out.
    Omitted,
    /// The callee's first parameter is optional and the first argument is
    /// supplied for it.
    Supplied,
}

/// One node of a binding's body: the core language the backend lowers.
/// Children precede their parents in the pool.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BodyNode {
    /// The parameter of an enclosing function, counted from the outermost.
    Local(u32),
    /// The value a `Value` obligation resolved.
    Free(ObligationIdx),
    /// An application to unlabelled arguments, after an optional one.
    Apply {
        /// The callee.
        funct: BodyIdx,
        /// The arguments: a range of the argument pool.
        args: u32,
        /// Number of arguments.
        len: u16,
        /// Whether the call is written as a partial application (`f(a, ...)`).
        partial: bool,
        /// The optional first argument.
        optional: OptionalArg,
    },
    /// A function of one parameter.
    Function {
        /// The parameter's name.
        param: StrIdx,
        /// The function's body.
        body: BodyIdx,
    },
    /// A field access.
    Field {
        /// The record.
        record: BodyIdx,
        /// The `Label` obligation.
        label: ObligationIdx,
    },
    /// A record expression that writes every field: field `i` has the label
    /// of obligation `labels + i` and the value of argument `fields + i`.
    Record {
        /// The first `Label` obligation.
        labels: ObligationIdx,
        /// The values: a range of the argument pool.
        fields: u32,
        /// Number of fields.
        len: u32,
    },
    /// A constructor applied to one argument or to none.
    Construct {
        /// The `Constructor` obligation.
        constructor: ObligationIdx,
        /// The argument, when the obligation has one.
        arg: BodyIdx,
    },
    /// A tuple.
    Tuple {
        /// The components: a range of the argument pool.
        args: u32,
        /// Number of components.
        len: u32,
    },
    /// An array literal.
    Array {
        /// The elements: a range of the argument pool.
        args: u32,
        /// Number of elements.
        len: u32,
    },
    /// A string constant the derive made.
    Str(StrIdx),
    /// The constant of a `Literal` obligation.
    Literal(ObligationIdx),
    /// A match whose cases are total: each tests one constructor or is a
    /// wildcard, or is a nested pattern.
    Switch {
        /// The scrutinee.
        scrutinee: BodyIdx,
        /// The cases: a range of the case pool.
        cases: u32,
        /// Number of cases.
        len: u16,
    },
    /// A constructor applied to two or more arguments: as many as its
    /// obligation's `args`, a range of the argument pool.
    ConstructArgs {
        /// The `Constructor` obligation.
        constructor: ObligationIdx,
        /// The arguments: a range of the argument pool.
        args: u32,
    },
    /// An integer constant the derive made.
    Int(i32),
    /// `if cond { then } else { else_ }`.
    If {
        /// The condition.
        cond: BodyIdx,
        /// The value when it holds.
        then: BodyIdx,
        /// The value otherwise.
        else_: BodyIdx,
    },
    /// `let param = value; body`: `body` sees `param` as its innermost
    /// local.
    Let {
        /// The bound variable's name.
        param: StrIdx,
        /// The bound value.
        value: BodyIdx,
        /// The body.
        body: BodyIdx,
    },
    /// A copy of the record `base` with the field of the `Label`
    /// obligation `label` set to `value`: `{...base, label: value}`.
    Update {
        /// The record copied.
        base: BodyIdx,
        /// The `Label` obligation of the field written.
        label: ObligationIdx,
        /// The field's new value.
        value: BodyIdx,
    },
}

/// The pattern of a case.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CasePattern {
    /// `_`.
    Any,
    /// A constructor applied to a variable, which the case's body sees as
    /// its innermost local.
    Construct {
        /// The `Constructor` obligation.
        constructor: ObligationIdx,
        /// The variable's name.
        binder: StrIdx,
    },
    /// A pattern of the pattern pool. Its variables are the case body's
    /// locals in prefix order: the last is the innermost.
    Nested(PatIdx),
}

/// One node of a case pattern. A pattern is stored in prefix order: a node
/// is followed by its sub-patterns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PatNode {
    /// `_`.
    Any,
    /// A variable.
    Var(StrIdx),
    /// A constructor, followed by as many sub-patterns as its obligation's
    /// `args`.
    Construct(ObligationIdx),
    /// A tuple of the `len` sub-patterns that follow.
    Tuple {
        /// Number of components.
        len: u16,
    },
    /// A closed record pattern of an inline record that names every field
    /// in order: field `i` has the label of obligation `labels + i` and the
    /// `i`-th of the `len` sub-patterns that follow.
    Record {
        /// The first `Label` obligation.
        labels: ObligationIdx,
        /// Number of fields.
        len: u16,
    },
    /// The empty array `[]`.
    EmptyArray,
    /// A string constant the derive made.
    Str(StrIdx),
}

/// One case of a `Switch`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Case {
    /// The pattern.
    pub pattern: CasePattern,
    /// The body.
    pub body: BodyIdx,
}

/// Where the type of a binding comes from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeSource {
    /// The function type that remains of the value `obligation` resolved
    /// after `applied` leading parameters were supplied.
    ResultOf {
        /// A `Value` obligation of the binding.
        obligation: ObligationIdx,
        /// Number of parameters supplied.
        applied: u32,
    },
    /// The instance of a skeleton, made after the binding's obligations.
    Stated(SkeletonIdx),
}

/// One binding of a derived item.
#[derive(Debug, Clone)]
pub struct Binding {
    /// The bound name.
    pub name: StrIdx,
    /// Attributes of the binding, scoped around its checks as a `let`
    /// binding's are.
    pub attributes: Attributes,
    /// The obligations, in typing order.
    pub obligations: Span,
    /// The root of the body: a `BodyNode::Function`.
    pub body: BodyIdx,
    /// Number of skeleton variable slots the binding uses.
    pub vars: u32,
    /// Where the binding's type comes from.
    pub ty: TypeSource,
}

/// The plan pools of one `ParseArena`.
#[derive(Debug, Default)]
pub struct Plans {
    items: Vec<Item>,
    bindings: Vec<Binding>,
    obligations: Vec<Obligation>,
    skeletons: Vec<SkeletonNode>,
    body: Vec<BodyNode>,
    body_args: Vec<BodyIdx>,
    cases: Vec<Case>,
    patterns: Vec<PatNode>,
}

impl Plans {
    /// Number of derived items. Cost: O(1).
    pub fn item_count(&self) -> usize {
        self.items.len()
    }

    /// Number of bindings of all items. Cost: O(1).
    pub fn binding_count(&self) -> usize {
        self.bindings.len()
    }

    /// Number of obligations of all items: the size of a table indexed by
    /// `ObligationIdx`. Cost: O(1).
    pub fn obligation_count(&self) -> usize {
        self.obligations.len()
    }

    /// Number of body nodes of all items. Cost: O(1).
    pub fn body_count(&self) -> usize {
        self.body.len()
    }

    /// The handle the next pushed binding gets. Cost: O(1).
    pub fn next_binding(&self) -> BindingIdx {
        BindingIdx(self.bindings.len() as u32)
    }

    /// The handle the next pushed obligation gets. Cost: O(1).
    pub fn next_obligation(&self) -> ObligationIdx {
        ObligationIdx(self.obligations.len() as u32)
    }

    /// Append an item whose bindings are the `len` most recently pushed.
    /// Cost: O(1) amortised; one slot, no other allocation.
    pub fn push_item(&mut self, first: BindingIdx) -> DerivedIdx {
        let idx = DerivedIdx(self.items.len() as u32);
        self.items.push(Item {
            bindings: Span {
                start: first.0,
                len: self.bindings.len() as u32 - first.0,
            },
        });
        idx
    }

    /// Append a binding. Cost: O(1) amortised; one slot.
    pub fn push_binding(&mut self, binding: Binding) -> BindingIdx {
        let idx = self.next_binding();
        self.bindings.push(binding);
        idx
    }

    /// Append an obligation. Cost: O(1) amortised; one 16-byte slot.
    pub fn push_obligation(&mut self, obligation: Obligation) -> ObligationIdx {
        let idx = self.next_obligation();
        self.obligations.push(obligation);
        idx
    }

    /// The handle the next pushed skeleton node gets. Cost: O(1).
    pub fn next_skeleton(&self) -> SkeletonIdx {
        SkeletonIdx(self.skeletons.len() as u32)
    }

    /// Append one skeleton node; a skeleton is the node and the children
    /// pushed after it. Cost: O(1) amortised; one 8-byte slot.
    pub fn push_skeleton(&mut self, node: SkeletonNode) -> SkeletonIdx {
        let idx = SkeletonIdx(self.skeletons.len() as u32);
        self.skeletons.push(node);
        idx
    }

    /// Append a body node whose children were pushed before it.
    /// Cost: O(1) amortised; one 16-byte slot.
    pub fn push_body(&mut self, node: BodyNode) -> BodyIdx {
        let idx = BodyIdx(self.body.len() as u32);
        self.body.push(node);
        idx
    }

    /// Append an application of `funct` to `args`.
    /// Cost: O(arguments): one argument slot each and one node slot.
    pub fn push_apply(&mut self, funct: BodyIdx, args: &[BodyIdx], partial: bool) -> BodyIdx {
        let start = self.body_args.len() as u32;
        self.body_args.extend_from_slice(args);
        self.push_body(BodyNode::Apply {
            funct,
            args: start,
            len: args.len() as u16,
            partial,
            optional: OptionalArg::Absent,
        })
    }

    /// Append `args` to the argument pool: the start of their range.
    /// Cost: O(arguments), one slot each.
    pub fn push_args(&mut self, args: &[BodyIdx]) -> u32 {
        let start = self.body_args.len() as u32;
        self.body_args.extend_from_slice(args);
        start
    }

    /// Append the cases of one `Switch`: the start of their range.
    /// Cost: O(cases), one 16-byte slot each.
    pub fn push_cases(&mut self, cases: &[Case]) -> u32 {
        let start = self.cases.len() as u32;
        self.cases.extend_from_slice(cases);
        start
    }

    /// Append one pattern node; a pattern is the node and the sub-patterns
    /// pushed after it. Cost: O(1) amortised; one 8-byte slot.
    pub fn push_pattern(&mut self, node: PatNode) -> PatIdx {
        let idx = PatIdx(self.patterns.len() as u32);
        self.patterns.push(node);
        idx
    }

    /// Number of pattern nodes of all items. Cost: O(1).
    pub fn pattern_count(&self) -> usize {
        self.patterns.len()
    }

    /// The pattern pool from `idx` on: the pattern's nodes in prefix order,
    /// then whatever follows it. Cost: O(1).
    #[inline]
    pub fn pattern_from(&self, idx: PatIdx) -> &[PatNode] {
        &self.patterns[idx.index()..]
    }

    /// The cases of a `Switch` node. Cost: O(1).
    #[inline]
    pub fn cases(&self, start: u32, len: u16) -> &[Case] {
        &self.cases[start as usize..start as usize + len as usize]
    }

    /// A range of the argument pool. Cost: O(1).
    #[inline]
    pub fn args(&self, start: u32, len: u32) -> &[BodyIdx] {
        &self.body_args[start as usize..(start + len) as usize]
    }

    /// The item of a handle. Cost: O(1).
    #[inline]
    pub fn item(&self, idx: DerivedIdx) -> Item {
        self.items[idx.index()]
    }

    /// The bindings of an item, in declaration order. Cost: O(1).
    #[inline]
    pub fn bindings(&self, item: Item) -> &[Binding] {
        &self.bindings[item.bindings.range()]
    }

    /// The obligation of a handle. Cost: O(1).
    #[inline]
    pub fn obligation(&self, idx: ObligationIdx) -> Obligation {
        self.obligations[idx.index()]
    }

    /// The skeleton pool from `idx` on: the skeleton's nodes in prefix order,
    /// then whatever follows it. Cost: O(1).
    #[inline]
    pub fn skeleton_from(&self, idx: SkeletonIdx) -> &[SkeletonNode] {
        &self.skeletons[idx.index()..]
    }

    /// The body node of a handle. Cost: O(1).
    #[inline]
    pub fn body(&self, idx: BodyIdx) -> BodyNode {
        self.body[idx.index()]
    }

    /// The arguments of an application node. Cost: O(1).
    #[inline]
    pub fn apply_args(&self, start: u32, len: u16) -> &[BodyIdx] {
        &self.body_args[start as usize..start as usize + len as usize]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::size_of;

    #[test]
    fn sizes_are_pinned() {
        assert_eq!(size_of::<DerivedIdx>(), 4);
        assert_eq!(size_of::<BindingIdx>(), 4);
        assert_eq!(size_of::<ObligationIdx>(), 4);
        assert_eq!(size_of::<SkeletonIdx>(), 4);
        assert_eq!(size_of::<BodyIdx>(), 4);
        assert_eq!(size_of::<PatIdx>(), 4);
        assert_eq!(size_of::<PatNode>(), 8);
        assert_eq!(size_of::<CasePattern>(), 12);
        assert_eq!(size_of::<Obligation>(), 16);
        assert_eq!(size_of::<BodyNode>(), 16);
        assert_eq!(size_of::<Case>(), 16);
        assert_eq!(size_of::<TypeSource>(), 12);
        assert_eq!(size_of::<SkeletonNode>(), 8);
        assert_eq!(size_of::<Item>(), 8);
        assert_eq!(size_of::<Binding>(), 40);
    }

    /// Pushing is one slot per element: 10,000 obligations, skeleton nodes
    /// and body nodes occupy exactly 10,000 slots of each pool, and an
    /// application's arguments exactly one argument slot each.
    #[test]
    fn pools_hold_one_slot_per_element() {
        let mut plans = Plans::default();
        let first = plans.next_binding();
        let name = LidentIdx(0);
        let mut args = Vec::new();
        for i in 0..10_000u32 {
            let skeleton = plans.push_skeleton(SkeletonNode::Var(i));
            let obligation = plans.push_obligation(Obligation::Value {
                name,
                name_loc: LocIdx(0),
                skeleton,
                expr_loc: ExprLoc::Dummy,
                called: false,
            });
            args.push(plans.push_body(BodyNode::Free(obligation)));
        }
        let funct = args[0];
        let apply = plans.push_apply(funct, &args[1..], false);
        let body = plans.push_body(BodyNode::Function {
            param: StrIdx(0),
            body: apply,
        });
        plans.push_binding(Binding {
            name: StrIdx(0),
            attributes: Attributes::new(),
            obligations: Span { start: 0, len: 10_000 },
            body,
            vars: 10_000,
            ty: TypeSource::ResultOf {
                obligation: ObligationIdx(0),
                applied: 0,
            },
        });
        let item = plans.push_item(first);
        assert_eq!(plans.obligation_count(), 10_000);
        assert_eq!(plans.skeletons.len(), 10_000);
        assert_eq!(plans.body.len(), 10_002);
        assert_eq!(plans.body_args.len(), 9_999);
        let item = plans.item(item);
        assert_eq!(plans.bindings(item).len(), 1);
        assert_eq!(plans.bindings(item)[0].obligations.range(), 0..10_000);
        let BodyNode::Apply { args, len, .. } = plans.body(apply) else {
            panic!("an application")
        };
        assert_eq!(plans.apply_args(args, len), &args_of(&plans)[..]);
        fn args_of(plans: &Plans) -> Vec<BodyIdx> {
            (1..10_000).map(BodyIdx).collect::<Vec<_>>().into_iter().filter(|idx| {
                matches!(plans.body(*idx), BodyNode::Free(_))
            }).collect()
        }
    }
}
