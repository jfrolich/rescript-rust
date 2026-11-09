//! Arena storage for the JS IR.
//!
//! One [`JsArena`] holds every JS IR node of a compilation unit. Expression
//! and statement nodes are 16-byte `Copy` kinds in dense `Vec`s and refer to
//! each other through `u32` handles ([`Expr`], [`Stmt`]). Everything that
//! does not fit in 16 bytes lives in per-kind side tables:
//!
//! - child lists in span pools ([`ExprList`], [`StmtList`], [`PropList`],
//!   [`IdentList`]),
//! - strings in one text buffer ([`StrId`]),
//! - identifiers, numbers, call info, function headers, tag info, variable
//!   declarations, loops, switches and `try` blocks in their own tables,
//! - comments and source locations, which most nodes lack, in a cold table.
//!
//! Nodes are immutable once pushed. OCaml's `J.expression`/`J.statement` is
//! an immutable tree whose passes rebuild changed spines and share the rest;
//! the arena gives the same semantics: a pass that rewrites a node pushes a
//! new node and keeps every unchanged child handle, so a handle may be
//! referenced from several parents. The one mutable payload is a variable
//! declaration's `ident_info`, which OCaml also mutates in place
//! (`js_pass_flatten_and_mark_dead.ml`). The whole arena is freed at once
//! with its compilation unit.

use std::num::NonZeroU32;

use crate::ident::Ident;
use crate::lambda::lam_tag_info::TagInfo;
use crate::lambda::{LamLoc, SwitchCaseTag};

use super::op::{BinOp, IdentInfo, LengthObject, MutableFlag, Number, Property};
use super::{CallInfo, ForDirection, JsRawInfo, ModuleId, RecordRestField};

macro_rules! handle {
    ($(#[$m:meta])* $name:ident) => {
        $(#[$m])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        #[repr(transparent)]
        pub struct $name(NonZeroU32);

        impl $name {
            #[inline]
            fn new(index: usize) -> Self {
                $name(NonZeroU32::new(checked_u32(index)).expect("slot 0 is reserved"))
            }
            #[inline]
            pub fn index(self) -> usize {
                self.0.get() as usize
            }
        }
    };
}

handle!(
    /// An expression node. Interpret only through the arena that created it.
    Expr
);
handle!(
    /// A statement node. Interpret only through the arena that created it.
    Stmt
);
handle!(
    /// A list of expressions in the expression list pool.
    ExprList
);
handle!(
    /// A list of statements (a JS block) in the statement list pool.
    StmtList
);
handle!(
    /// A list of object-literal properties.
    PropList
);
handle!(
    /// A list of identifiers (function parameters).
    IdentList
);
handle!(
    /// A string in the arena's text buffer.
    StrId
);
handle!(IdentId);
handle!(NumId);
handle!(CallId);
handle!(FunId);
handle!(TagId);
handle!(QualId);
handle!(RawId);
handle!(TemplateId);
handle!(SegmentsId);
handle!(TaggedId);
handle!(RestId);
handle!(VarId);
handle!(ForRangeId);
handle!(ForOfId);
handle!(IntSwitchId);
handle!(StringSwitchId);
handle!(TryId);
handle!(ColdId);

#[inline]
fn checked_u32(n: usize) -> u32 {
    u32::try_from(n).expect("JS arena exceeds u32 capacity")
}

/// `Option<i32>` field position of a static index, packed into four bytes.
/// `i32::MIN` encodes `None`; positions are record field indices and are
/// never negative.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FieldPos(i32);

impl FieldPos {
    pub const NONE: FieldPos = FieldPos(i32::MIN);

    pub fn new(pos: Option<i32>) -> Self {
        match pos {
            Some(pos) => {
                assert!(pos != i32::MIN, "field position out of range");
                FieldPos(pos)
            }
            None => FieldPos::NONE,
        }
    }

    pub fn get(self) -> Option<i32> {
        (self.0 != i32::MIN).then_some(self.0)
    }
}

/// Property name of an object literal entry (`Js_op.property_name`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropName {
    Lit(StrId),
    Symbol,
}

/// Expression node kinds (`J.expression_desc`).
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ExprKind {
    Length(Expr, LengthObject),
    IsNullOrUndefined(Expr),
    StringAppend(Expr, Expr),
    Bool(bool),
    Typeof(Expr),
    In(Expr, Expr),
    JsNot(Expr),
    JsBnot(Expr),
    Seq(Expr, Expr),
    Cond(Expr, Expr, Expr),
    Bin(BinOp, Expr, Expr),
    FlatCall(Expr, Expr),
    Call(Expr, ExprList, CallId),
    StringIndex(Expr, Expr),
    ArrayIndex(Expr, Expr),
    TaggedTemplate(Expr, TaggedId, ExprList),
    InterpolatedTemplate(SegmentsId, ExprList),
    StaticIndex(Expr, StrId, FieldPos),
    New(Expr, Option<ExprList>),
    Var(IdentId),
    Qualified(QualId),
    Fun(FunId),
    Str(StrId),
    TemplateLiteral(TemplateId),
    JsonLiteral(StrId),
    RawJsCode(RawId),
    Array(ExprList, MutableFlag),
    OptionalBlock(Expr, bool),
    CamlBlock(ExprList, MutableFlag, TagId),
    CamlBlockTag(Expr, StrId),
    Number(NumId),
    Object(Option<Expr>, PropList),
    Undefined { is_unit: bool },
    Null,
    Await(Expr),
    Spread(Expr),
    RecordRest(RestId, Expr),
}

/// Statement node kinds (`J.statement_desc`).
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StmtKind {
    Block(StmtList),
    Variable(VarId),
    Exp(Expr),
    If(Expr, StmtList, StmtList),
    /// The optional label is attached when a nested switch emits a labeled
    /// `break`/`continue` targeting this loop.
    While(Option<StrId>, Expr, StmtList),
    ForRange(ForRangeId),
    ForOf(ForOfId),
    ForAwaitOf(ForOfId),
    Continue(Option<StrId>),
    Break(Option<StrId>),
    Return(Expr),
    IntSwitch(Expr, IntSwitchId),
    StringSwitch(Expr, StringSwitchId),
    Throw(Expr),
    Try(TryId),
    Debugger,
}

#[derive(Debug, Clone, Copy)]
struct ExprNode {
    kind: ExprKind,
    cold: Option<ColdId>,
}

#[derive(Debug, Clone, Copy)]
struct StmtNode {
    kind: StmtKind,
    cold: Option<ColdId>,
}

/// Comment and source location of a node; most nodes have neither.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct Cold {
    pub comment: Option<StrId>,
    pub source_loc: Option<LamLoc>,
}

/// Function expression header (`J.Fun`). The printer computes the captured
/// identifiers (OCaml's `Js_fun_env`) from the body.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct FunInfo {
    pub is_method: bool,
    pub params: IdentList,
    pub body: StmtList,
    pub return_unit: bool,
    pub async_: bool,
    pub directive: Option<StrId>,
}

/// Variable declaration (`J.variable_declaration`).
#[derive(Debug, Clone)]
pub struct VarDecl {
    pub ident: Ident,
    pub value: Option<Expr>,
    pub property: Property,
    pub ident_info: IdentInfo,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ForRangeInfo {
    pub label: Option<StrId>,
    pub init: Option<Expr>,
    pub end: Expr,
    pub ident: IdentId,
    pub direction: ForDirection,
    pub body: StmtList,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ForOfInfo {
    pub label: Option<StrId>,
    pub ident: IdentId,
    pub iterable: Expr,
    pub body: StmtList,
}

/// Switch case clause (`J.case_clause`).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Clause {
    pub body: StmtList,
    pub should_break: bool,
    pub comment: Option<StrId>,
    pub source_loc: Option<LamLoc>,
}

#[derive(Debug, Clone)]
pub struct StringClauseInfo {
    pub tag_type: SwitchCaseTag,
    pub clause: Clause,
}

#[derive(Debug, Clone)]
pub struct IntSwitchInfo {
    pub clauses: Vec<(i32, Clause)>,
    pub default: Option<StmtList>,
}

#[derive(Debug, Clone)]
pub struct StringSwitchInfo {
    pub clauses: Vec<StringClauseInfo>,
    pub default: Option<StmtList>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TryInfo {
    pub body: StmtList,
    pub catch: Option<(IdentId, StmtList)>,
    pub finally: Option<StmtList>,
}

#[derive(Debug, Clone, Copy)]
struct Span {
    start: u32,
    len: u32,
}

impl Span {
    const EMPTY: Span = Span { start: 0, len: 0 };

    #[inline]
    fn range(self) -> std::ops::Range<usize> {
        self.start as usize..(self.start + self.len) as usize
    }
}

/// A pool of lists: the items of every list stored back to back, plus one
/// span per list. Index 0 is reserved, index 1 is the shared empty list.
#[derive(Debug, Clone)]
struct ListPool<T> {
    items: Vec<T>,
    spans: Vec<Span>,
}

impl<T: Clone> ListPool<T> {
    fn new() -> Self {
        ListPool {
            items: Vec::new(),
            spans: vec![Span::EMPTY, Span::EMPTY],
        }
    }

    fn push_slice(&mut self, items: &[T]) -> usize {
        if items.is_empty() {
            return 1;
        }
        let start = checked_u32(self.items.len());
        self.items.extend_from_slice(items);
        self.spans.push(Span {
            start,
            len: checked_u32(items.len()),
        });
        self.spans.len() - 1
    }

    fn push_iter(&mut self, items: impl IntoIterator<Item = T>) -> usize {
        let start = self.items.len();
        self.items.extend(items);
        let len = self.items.len() - start;
        if len == 0 {
            return 1;
        }
        self.spans.push(Span {
            start: checked_u32(start),
            len: checked_u32(len),
        });
        self.spans.len() - 1
    }

    #[inline]
    fn get(&self, index: usize) -> &[T] {
        &self.items[self.spans[index].range()]
    }
}

/// A table with slot 0 reserved, so handles can use `NonZeroU32`.
#[derive(Debug, Clone)]
struct Table<T> {
    rows: Vec<T>,
}

impl<T> Table<T> {
    fn new(dummy: T) -> Self {
        Table { rows: vec![dummy] }
    }
    #[inline]
    fn push(&mut self, row: T) -> usize {
        self.rows.push(row);
        self.rows.len() - 1
    }
    #[inline]
    fn get(&self, index: usize) -> &T {
        &self.rows[index]
    }
    #[inline]
    fn get_mut(&mut self, index: usize) -> &mut T {
        &mut self.rows[index]
    }
    fn len(&self) -> usize {
        self.rows.len()
    }
}

/// Storage for the JS IR of one compilation unit. See the module docs.
#[derive(Debug, Clone)]
pub struct JsArena {
    exprs: Table<ExprNode>,
    stmts: Table<StmtNode>,
    expr_lists: ListPool<Expr>,
    stmt_lists: ListPool<Stmt>,
    prop_lists: ListPool<(PropName, Expr)>,
    ident_lists: ListPool<Ident>,
    text: String,
    strs: Table<Span>,
    idents: Table<Ident>,
    numbers: Table<Number>,
    calls: Table<CallInfo>,
    funs: Table<FunInfo>,
    tags: Table<TagInfo>,
    quals: Table<(ModuleId, Option<String>)>,
    raws: Table<JsRawInfo>,
    templates: Table<crate::string_literal::TemplateSegment>,
    segments: Table<Vec<crate::string_literal::TemplateSegment>>,
    tagged: Table<Vec<String>>,
    rests: Table<Vec<RecordRestField>>,
    vars: Table<VarDecl>,
    for_ranges: Table<ForRangeInfo>,
    for_ofs: Table<ForOfInfo>,
    int_switches: Table<IntSwitchInfo>,
    string_switches: Table<StringSwitchInfo>,
    tries: Table<TryInfo>,
    colds: Table<Cold>,
    /// Scratch stacks for rebuilding lists without a temporary `Vec` per
    /// node. A user records the length as a mark, pushes above it and
    /// truncates back to the mark before returning, so nested users stack.
    expr_scratch: Vec<Expr>,
    stmt_scratch: Vec<Stmt>,
}

impl Default for JsArena {
    fn default() -> Self {
        Self::new()
    }
}

impl JsArena {
    pub fn new() -> Self {
        let dummy_ident = Ident::new("", 0, crate::ident::IdentFlags::NONE);
        let dummy_expr = ExprNode {
            kind: ExprKind::Null,
            cold: None,
        };
        let dummy_stmt = StmtNode {
            kind: StmtKind::Debugger,
            cold: None,
        };
        let empty_list = StmtList(NonZeroU32::MIN);
        JsArena {
            exprs: Table::new(dummy_expr),
            stmts: Table::new(dummy_stmt),
            expr_lists: ListPool::new(),
            stmt_lists: ListPool::new(),
            prop_lists: ListPool::new(),
            ident_lists: ListPool::new(),
            text: String::new(),
            strs: Table::new(Span::EMPTY),
            idents: Table::new(dummy_ident),
            numbers: Table::new(Number::int(0)),
            calls: Table::new(CallInfo::default()),
            funs: Table::new(FunInfo {
                is_method: false,
                params: IdentList(NonZeroU32::MIN),
                body: empty_list,
                return_unit: false,
                async_: false,
                directive: None,
            }),
            tags: Table::new(TagInfo::Tuple),
            quals: Table::new((
                ModuleId {
                    id: dummy_ident,
                    kind: super::Kind::Ml,
                    dynamic_import: false,
                },
                None,
            )),
            raws: Table::new(JsRawInfo {
                code: String::new(),
                is_stmt: false,
            }),
            templates: Table::new(crate::string_literal::template_from_semantic("")),
            segments: Table::new(Vec::new()),
            tagged: Table::new(Vec::new()),
            rests: Table::new(Vec::new()),
            vars: Table::new(VarDecl {
                ident: dummy_ident,
                value: None,
                property: Property::Strict,
                ident_info: IdentInfo::default(),
            }),
            for_ranges: Table::new(ForRangeInfo {
                label: None,
                init: None,
                end: Expr(NonZeroU32::MIN),
                ident: IdentId(NonZeroU32::MIN),
                direction: ForDirection::Upto,
                body: empty_list,
            }),
            for_ofs: Table::new(ForOfInfo {
                label: None,
                ident: IdentId(NonZeroU32::MIN),
                iterable: Expr(NonZeroU32::MIN),
                body: empty_list,
            }),
            int_switches: Table::new(IntSwitchInfo {
                clauses: Vec::new(),
                default: None,
            }),
            string_switches: Table::new(StringSwitchInfo {
                clauses: Vec::new(),
                default: None,
            }),
            tries: Table::new(TryInfo {
                body: empty_list,
                catch: None,
                finally: None,
            }),
            colds: Table::new(Cold::default()),
            expr_scratch: Vec::new(),
            stmt_scratch: Vec::new(),
        }
    }

    /// Number of expression and statement nodes, for diagnostics and tests.
    pub fn node_counts(&self) -> (usize, usize) {
        (self.exprs.len() - 1, self.stmts.len() - 1)
    }

    // ---- cold data -------------------------------------------------------

    fn cold_of(&mut self, comment: Option<StrId>, source_loc: Option<LamLoc>) -> Option<ColdId> {
        if comment.is_none() && source_loc.is_none() {
            None
        } else {
            Some(ColdId::new(self.colds.push(Cold {
                comment,
                source_loc,
            })))
        }
    }

    #[inline]
    fn cold(&self, cold: Option<ColdId>) -> Cold {
        cold.map_or(Cold::default(), |id| *self.colds.get(id.index()))
    }

    // ---- expressions -----------------------------------------------------

    /// Push an expression without comment or location.
    #[inline]
    pub fn expr(&mut self, kind: ExprKind) -> Expr {
        Expr::new(self.exprs.push(ExprNode { kind, cold: None }))
    }

    /// Push an expression with the given cold data.
    pub fn expr_with(&mut self, kind: ExprKind, cold: Cold) -> Expr {
        let cold = self.cold_of(cold.comment, cold.source_loc);
        Expr::new(self.exprs.push(ExprNode { kind, cold }))
    }

    /// Push an expression with a comment.
    pub fn expr_commented(&mut self, kind: ExprKind, comment: &str) -> Expr {
        let comment = Some(self.str(comment));
        self.expr_with(
            kind,
            Cold {
                comment,
                source_loc: None,
            },
        )
    }

    #[inline]
    pub fn ek(&self, e: Expr) -> ExprKind {
        self.exprs.get(e.index()).kind
    }

    #[inline]
    pub fn expr_cold(&self, e: Expr) -> Cold {
        self.cold(self.exprs.get(e.index()).cold)
    }

    pub fn expr_comment(&self, e: Expr) -> Option<&str> {
        self.expr_cold(e).comment.map(|s| self.text(s))
    }

    pub fn expr_loc(&self, e: Expr) -> Option<LamLoc> {
        self.expr_cold(e).source_loc
    }

    /// `e` with a different kind and the same comment and location. Returns
    /// `e` itself when the kind is unchanged.
    pub fn rekind_expr(&mut self, e: Expr, kind: ExprKind) -> Expr {
        let node = *self.exprs.get(e.index());
        if node.kind == kind {
            return e;
        }
        Expr::new(self.exprs.push(ExprNode {
            kind,
            cold: node.cold,
        }))
    }

    /// `e` with replaced cold data.
    pub fn with_expr_cold(&mut self, e: Expr, cold: Cold) -> Expr {
        let node = *self.exprs.get(e.index());
        if self.cold(node.cold) == cold {
            return e;
        }
        self.expr_with(node.kind, cold)
    }

    /// `e` with its comment replaced.
    pub fn with_expr_comment(&mut self, e: Expr, comment: Option<&str>) -> Expr {
        let mut cold = self.expr_cold(e);
        cold.comment = comment.map(|c| self.str(c));
        self.with_expr_cold(e, cold)
    }

    /// `e` with its source location replaced.
    pub fn with_expr_loc(&mut self, e: Expr, source_loc: Option<LamLoc>) -> Expr {
        let mut cold = self.expr_cold(e);
        cold.source_loc = source_loc;
        self.with_expr_cold(e, cold)
    }

    // ---- statements ------------------------------------------------------

    #[inline]
    pub fn stmt(&mut self, kind: StmtKind) -> Stmt {
        Stmt::new(self.stmts.push(StmtNode { kind, cold: None }))
    }

    pub fn stmt_with(&mut self, kind: StmtKind, cold: Cold) -> Stmt {
        let cold = self.cold_of(cold.comment, cold.source_loc);
        Stmt::new(self.stmts.push(StmtNode { kind, cold }))
    }

    #[inline]
    pub fn sk(&self, s: Stmt) -> StmtKind {
        self.stmts.get(s.index()).kind
    }

    #[inline]
    pub fn stmt_cold(&self, s: Stmt) -> Cold {
        self.cold(self.stmts.get(s.index()).cold)
    }

    pub fn stmt_comment(&self, s: Stmt) -> Option<&str> {
        self.stmt_cold(s).comment.map(|c| self.text(c))
    }

    pub fn stmt_loc(&self, s: Stmt) -> Option<LamLoc> {
        self.stmt_cold(s).source_loc
    }

    /// `s` with a different kind and the same comment and location.
    pub fn rekind_stmt(&mut self, s: Stmt, kind: StmtKind) -> Stmt {
        let node = *self.stmts.get(s.index());
        if node.kind == kind {
            return s;
        }
        Stmt::new(self.stmts.push(StmtNode {
            kind,
            cold: node.cold,
        }))
    }

    pub fn with_stmt_cold(&mut self, s: Stmt, cold: Cold) -> Stmt {
        let node = *self.stmts.get(s.index());
        if self.cold(node.cold) == cold {
            return s;
        }
        self.stmt_with(node.kind, cold)
    }

    pub fn with_stmt_comment(&mut self, s: Stmt, comment: Option<&str>) -> Stmt {
        let mut cold = self.stmt_cold(s);
        cold.comment = comment.map(|c| self.str(c));
        self.with_stmt_cold(s, cold)
    }

    pub fn with_stmt_loc(&mut self, s: Stmt, source_loc: Option<LamLoc>) -> Stmt {
        let mut cold = self.stmt_cold(s);
        cold.source_loc = source_loc;
        self.with_stmt_cold(s, cold)
    }

    // ---- lists -----------------------------------------------------------

    pub fn expr_list(&mut self, items: &[Expr]) -> ExprList {
        ExprList::new(self.expr_lists.push_slice(items))
    }

    pub fn expr_list_from(&mut self, items: impl IntoIterator<Item = Expr>) -> ExprList {
        ExprList::new(self.expr_lists.push_iter(items))
    }

    #[inline]
    pub fn exprs(&self, list: ExprList) -> &[Expr] {
        self.expr_lists.get(list.index())
    }

    pub fn stmt_list(&mut self, items: &[Stmt]) -> StmtList {
        StmtList::new(self.stmt_lists.push_slice(items))
    }

    pub fn stmt_list_from(&mut self, items: impl IntoIterator<Item = Stmt>) -> StmtList {
        StmtList::new(self.stmt_lists.push_iter(items))
    }

    /// The shared empty block.
    pub fn empty_block(&self) -> StmtList {
        StmtList(NonZeroU32::MIN)
    }

    /// The shared empty expression list.
    pub fn empty_exprs(&self) -> ExprList {
        ExprList(NonZeroU32::MIN)
    }

    #[inline]
    pub fn stmts(&self, list: StmtList) -> &[Stmt] {
        self.stmt_lists.get(list.index())
    }

    /// An owned copy of a block's statement handles, for passes that rebuild
    /// the block.
    pub fn block_vec(&self, list: StmtList) -> Vec<Stmt> {
        self.stmts(list).to_vec()
    }

    pub fn expr_vec(&self, list: ExprList) -> Vec<Expr> {
        self.exprs(list).to_vec()
    }

    /// The current top of the expression scratch stack.
    #[inline]
    pub fn expr_scratch_mark(&self) -> usize {
        self.expr_scratch.len()
    }

    #[inline]
    pub fn expr_scratch_push(&mut self, e: Expr) {
        self.expr_scratch.push(e);
    }

    /// Interns the scratch entries above `mark` as a list and pops them.
    pub fn expr_list_from_scratch(&mut self, mark: usize) -> ExprList {
        let list = ExprList::new(self.expr_lists.push_slice(&self.expr_scratch[mark..]));
        self.expr_scratch.truncate(mark);
        list
    }

    #[inline]
    pub fn expr_scratch_truncate(&mut self, mark: usize) {
        self.expr_scratch.truncate(mark);
    }

    /// The current top of the statement scratch stack.
    #[inline]
    pub fn stmt_scratch_mark(&self) -> usize {
        self.stmt_scratch.len()
    }

    #[inline]
    pub fn stmt_scratch_push(&mut self, s: Stmt) {
        self.stmt_scratch.push(s);
    }

    /// Interns the scratch entries above `mark` as a block and pops them.
    pub fn stmt_list_from_scratch(&mut self, mark: usize) -> StmtList {
        let list = StmtList::new(self.stmt_lists.push_slice(&self.stmt_scratch[mark..]));
        self.stmt_scratch.truncate(mark);
        list
    }

    #[inline]
    pub fn stmt_scratch_truncate(&mut self, mark: usize) {
        self.stmt_scratch.truncate(mark);
    }

    pub fn prop_list(&mut self, items: &[(PropName, Expr)]) -> PropList {
        PropList::new(self.prop_lists.push_slice(items))
    }

    pub fn prop_list_from(
        &mut self,
        items: impl IntoIterator<Item = (PropName, Expr)>,
    ) -> PropList {
        PropList::new(self.prop_lists.push_iter(items))
    }

    #[inline]
    pub fn props(&self, list: PropList) -> &[(PropName, Expr)] {
        self.prop_lists.get(list.index())
    }

    pub fn ident_list(&mut self, items: &[Ident]) -> IdentList {
        IdentList::new(self.ident_lists.push_slice(items))
    }

    #[inline]
    pub fn ident_slice(&self, list: IdentList) -> &[Ident] {
        self.ident_lists.get(list.index())
    }

    // ---- strings ---------------------------------------------------------

    pub fn str(&mut self, s: &str) -> StrId {
        let start = checked_u32(self.text.len());
        self.text.push_str(s);
        StrId::new(self.strs.push(Span {
            start,
            len: checked_u32(s.len()),
        }))
    }

    #[inline]
    pub fn text(&self, id: StrId) -> &str {
        &self.text[self.strs.get(id.index()).range()]
    }

    pub fn prop_name_text(&self, name: PropName) -> Option<&str> {
        match name {
            PropName::Lit(s) => Some(self.text(s)),
            PropName::Symbol => None,
        }
    }

    // ---- side tables -----------------------------------------------------

    pub fn ident_id(&mut self, id: Ident) -> IdentId {
        IdentId::new(self.idents.push(id))
    }

    #[inline]
    pub fn ident(&self, id: IdentId) -> Ident {
        *self.idents.get(id.index())
    }

    pub fn number_id(&mut self, n: Number) -> NumId {
        NumId::new(self.numbers.push(n))
    }

    #[inline]
    pub fn number(&self, id: NumId) -> &Number {
        self.numbers.get(id.index())
    }

    pub fn call_id(&mut self, info: CallInfo) -> CallId {
        CallId::new(self.calls.push(info))
    }

    #[inline]
    pub fn call_info(&self, id: CallId) -> &CallInfo {
        self.calls.get(id.index())
    }

    pub fn fun_id(&mut self, info: FunInfo) -> FunId {
        FunId::new(self.funs.push(info))
    }

    #[inline]
    pub fn fun(&self, id: FunId) -> FunInfo {
        *self.funs.get(id.index())
    }

    pub fn tag_id(&mut self, tag: TagInfo) -> TagId {
        TagId::new(self.tags.push(tag))
    }

    #[inline]
    pub fn tag(&self, id: TagId) -> &TagInfo {
        self.tags.get(id.index())
    }

    pub fn qual_id(&mut self, module: ModuleId, member: Option<String>) -> QualId {
        QualId::new(self.quals.push((module, member)))
    }

    #[inline]
    pub fn qual(&self, id: QualId) -> (&ModuleId, Option<&str>) {
        let (module, member) = self.quals.get(id.index());
        (module, member.as_deref())
    }

    pub fn raw_id(&mut self, info: JsRawInfo) -> RawId {
        RawId::new(self.raws.push(info))
    }

    #[inline]
    pub fn raw(&self, id: RawId) -> &JsRawInfo {
        self.raws.get(id.index())
    }

    pub fn template_id(&mut self, segment: crate::string_literal::TemplateSegment) -> TemplateId {
        TemplateId::new(self.templates.push(segment))
    }

    #[inline]
    pub fn template(&self, id: TemplateId) -> &crate::string_literal::TemplateSegment {
        self.templates.get(id.index())
    }

    pub fn segments_id(
        &mut self,
        segments: Vec<crate::string_literal::TemplateSegment>,
    ) -> SegmentsId {
        SegmentsId::new(self.segments.push(segments))
    }

    #[inline]
    pub fn segments(&self, id: SegmentsId) -> &[crate::string_literal::TemplateSegment] {
        self.segments.get(id.index())
    }

    pub fn tagged_id(&mut self, strings: Vec<String>) -> TaggedId {
        TaggedId::new(self.tagged.push(strings))
    }

    #[inline]
    pub fn tagged(&self, id: TaggedId) -> &[String] {
        self.tagged.get(id.index())
    }

    pub fn rest_id(&mut self, fields: Vec<RecordRestField>) -> RestId {
        RestId::new(self.rests.push(fields))
    }

    #[inline]
    pub fn rest(&self, id: RestId) -> &[RecordRestField] {
        self.rests.get(id.index())
    }

    pub fn var_id(&mut self, decl: VarDecl) -> VarId {
        VarId::new(self.vars.push(decl))
    }

    #[inline]
    pub fn var(&self, id: VarId) -> &VarDecl {
        self.vars.get(id.index())
    }

    /// The one in-place mutation the IR allows: OCaml's mutable
    /// `ident_info` field.
    pub fn var_ident_info_mut(&mut self, id: VarId) -> &mut IdentInfo {
        &mut self.vars.get_mut(id.index()).ident_info
    }

    pub fn for_range_id(&mut self, info: ForRangeInfo) -> ForRangeId {
        ForRangeId::new(self.for_ranges.push(info))
    }

    #[inline]
    pub fn for_range(&self, id: ForRangeId) -> ForRangeInfo {
        *self.for_ranges.get(id.index())
    }

    pub fn for_of_id(&mut self, info: ForOfInfo) -> ForOfId {
        ForOfId::new(self.for_ofs.push(info))
    }

    #[inline]
    pub fn for_of(&self, id: ForOfId) -> ForOfInfo {
        *self.for_ofs.get(id.index())
    }

    pub fn int_switch_id(&mut self, info: IntSwitchInfo) -> IntSwitchId {
        IntSwitchId::new(self.int_switches.push(info))
    }

    #[inline]
    pub fn int_switch(&self, id: IntSwitchId) -> &IntSwitchInfo {
        self.int_switches.get(id.index())
    }

    pub fn string_switch_id(&mut self, info: StringSwitchInfo) -> StringSwitchId {
        StringSwitchId::new(self.string_switches.push(info))
    }

    #[inline]
    pub fn string_switch(&self, id: StringSwitchId) -> &StringSwitchInfo {
        self.string_switches.get(id.index())
    }

    pub fn try_id(&mut self, info: TryInfo) -> TryId {
        TryId::new(self.tries.push(info))
    }

    #[inline]
    pub fn try_info(&self, id: TryId) -> TryInfo {
        *self.tries.get(id.index())
    }
}

/// An owned block under construction: statement handles that become a
/// [`StmtList`] when a node is built from them.
pub type Block = Vec<Stmt>;

impl StmtList {
    /// The shared empty block, valid in every arena.
    pub const EMPTY: StmtList = StmtList(NonZeroU32::MIN);
}

impl ExprList {
    /// The shared empty expression list, valid in every arena.
    pub const EMPTY: ExprList = ExprList(NonZeroU32::MIN);
}

/// A JS program: its arena plus the top-level statements (`J.program`).
#[derive(Debug, Clone)]
pub struct JsProgram {
    pub arena: JsArena,
    /// Program statements
    pub block: Vec<Stmt>,
    /// Exported identifiers
    pub exports: super::Exports,
    /// Set of exported identifiers
    pub export_set: ahash::AHashSet<Ident>,
    /// Idents that occupy printed names without emitting statements.
    pub name_reservations: Vec<Ident>,
}

#[cfg(test)]
impl JsProgram {
    /// A program over `block` and `exports`, owning `arena`.
    pub fn new_in(block: Vec<Stmt>, exports: super::Exports, arena: JsArena) -> Self {
        let export_set = exports.iter().copied().collect();
        JsProgram {
            arena,
            block,
            exports,
            export_set,
            name_reservations: Vec::new(),
        }
    }
}

/// A program with its dependencies (`J.deps_program`).
#[derive(Debug, Clone)]
pub struct JsDepsProgram {
    pub program: JsProgram,
    /// Required modules
    pub modules: super::RequiredModules,
    /// Side effect reason (None = no side effects)
    pub side_effect: Option<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn node_kinds_stay_small() {
        assert_eq!(std::mem::size_of::<ExprKind>(), 16);
        assert_eq!(std::mem::size_of::<StmtKind>(), 16);
        assert_eq!(std::mem::size_of::<ExprNode>(), 20);
        assert_eq!(std::mem::size_of::<StmtNode>(), 20);
        assert_eq!(std::mem::size_of::<Option<Expr>>(), 4);
    }

    #[test]
    fn empty_lists_share_one_handle() {
        let mut a = JsArena::new();
        assert_eq!(a.stmt_list(&[]), a.empty_block());
        assert_eq!(a.expr_list_from(std::iter::empty()), a.empty_exprs());
        let n = a.expr(ExprKind::Null);
        let l = a.expr_list(&[n, n]);
        assert_eq!(a.exprs(l), &[n, n]);
    }

    #[test]
    fn rekind_keeps_cold_data() {
        let mut a = JsArena::new();
        let e = a.expr_commented(ExprKind::Null, "c");
        let same = a.rekind_expr(e, ExprKind::Null);
        assert_eq!(same, e);
        let other = a.rekind_expr(e, ExprKind::Bool(true));
        assert_ne!(other, e);
        assert_eq!(a.expr_comment(other), Some("c"));
    }
}
