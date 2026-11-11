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
            /// The slot index of this handle in its table (never 0).
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
handle!(
    /// An identifier in the identifier table.
    IdentId
);
handle!(
    /// A number literal in the number table.
    NumId
);
handle!(
    /// Call metadata ([`CallInfo`]) of a call expression.
    CallId
);
handle!(
    /// A function header ([`FunInfo`]).
    FunId
);
handle!(
    /// Block tag info ([`TagInfo`]) of a `CamlBlock`.
    TagId
);
handle!(
    /// A module reference with an optional member name.
    QualId
);
handle!(
    /// Raw JavaScript code ([`JsRawInfo`]).
    RawId
);
handle!(
    /// The segment of a non-interpolated template literal.
    TemplateId
);
handle!(
    /// The segments of an interpolated template literal.
    SegmentsId
);
handle!(
    /// The raw string segments of a tagged template.
    TaggedId
);
handle!(
    /// The fields excluded by an object-rest expression.
    RestId
);
handle!(
    /// A variable declaration ([`VarDecl`]).
    VarId
);
handle!(
    /// An integer-range `for` loop ([`ForRangeInfo`]).
    ForRangeId
);
handle!(
    /// A `for...of` loop ([`ForOfInfo`]).
    ForOfId
);
handle!(
    /// The clauses of an integer `switch` ([`IntSwitchInfo`]).
    IntSwitchId
);
handle!(
    /// The clauses of a string `switch` ([`StringSwitchInfo`]).
    StringSwitchId
);
handle!(
    /// A `try` statement ([`TryInfo`]).
    TryId
);
handle!(
    /// A node's comment and source location ([`Cold`]).
    ColdId
);

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
    /// No known field position.
    pub const NONE: FieldPos = FieldPos(i32::MIN);

    /// Pack `pos`; panics on `i32::MIN`, which encodes `None`.
    pub fn new(pos: Option<i32>) -> Self {
        match pos {
            Some(pos) => {
                assert!(pos != i32::MIN, "field position out of range");
                FieldPos(pos)
            }
            None => FieldPos::NONE,
        }
    }

    /// The position, if known.
    pub fn get(self) -> Option<i32> {
        (self.0 != i32::MIN).then_some(self.0)
    }
}

/// Property name of an object literal entry (`Js_op.property_name`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PropName {
    /// A literal name, quoted when it is not a valid identifier.
    Lit(StrId),
    /// The well-known `[Symbol.for("name")]` key.
    Symbol,
}

/// Expression node kinds (`J.expression_desc`).
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ExprKind {
    /// `e.length` of an array, string, function or block.
    Length(Expr, LengthObject),
    /// `e == null`, true for both `null` and `undefined`.
    IsNullOrUndefined(Expr),
    /// String concatenation `a + b`.
    StringAppend(Expr, Expr),
    /// `true` or `false`.
    Bool(bool),
    /// `typeof e`.
    Typeof(Expr),
    /// `prop in obj`.
    In(Expr, Expr),
    /// Logical not, `!e`.
    JsNot(Expr),
    /// Bitwise not, `~e`.
    JsBnot(Expr),
    /// The comma expression `a, b`.
    Seq(Expr, Expr),
    /// The conditional `c ? a : b`.
    Cond(Expr, Expr, Expr),
    /// A binary operation or assignment.
    Bin(BinOp, Expr, Expr),
    /// `f.apply(null, args)`, a call with a runtime array of arguments.
    FlatCall(Expr, Expr),
    /// A call `f(args)` with its call metadata.
    Call(Expr, ExprList, CallId),
    /// Character access `s[i]`.
    StringIndex(Expr, Expr),
    /// Element access `a[i]` by an integer index.
    ArrayIndex(Expr, Expr),
    /// A tagged template: the tag, its raw string segments and the interpolated values.
    TaggedTemplate(Expr, TaggedId, ExprList),
    /// An untagged template with interpolations: its segments and values.
    InterpolatedTemplate(SegmentsId, ExprList),
    /// Property access `e.name` (or `e["name"]`), with the record field position if known.
    StaticIndex(Expr, StrId, FieldPos),
    /// `new C(args)`; `None` (no argument list) also prints as `new C()`.
    New(Expr, Option<ExprList>),
    /// A local variable.
    Var(IdentId),
    /// A module, or a member of one.
    Qualified(QualId),
    /// A function expression.
    Fun(FunId),
    /// A string value, printed with the compiler's own quoting.
    Str(StrId),
    /// A backquoted literal without interpolation, printed as written.
    TemplateLiteral(TemplateId),
    /// Validated JavaScript source of a `json` template payload.
    JsonLiteral(StrId),
    /// Code from `%raw` and similar, emitted verbatim.
    RawJsCode(RawId),
    /// An array literal.
    Array(ExprList, MutableFlag),
    /// `Some(e)`; `true` means the value is represented as `e` itself,
    /// otherwise it is wrapped with the runtime `Primitive_option.some`.
    OptionalBlock(Expr, bool),
    /// A record, tuple, variant or module block.
    CamlBlock(ExprList, MutableFlag, TagId),
    /// The tag field of a block, `e.TAG` (the field name is stored).
    CamlBlockTag(Expr, StrId),
    /// A number literal.
    Number(NumId),
    /// An object literal, optionally spreading a base object first.
    Object(Option<Expr>, PropList),
    /// `undefined`.
    Undefined {
        /// Whether this `undefined` stands for the unit value `()`.
        is_unit: bool,
    },
    /// `null`.
    Null,
    /// `await e`.
    Await(Expr),
    /// A spread `...e` in an argument or element list.
    Spread(Expr),
    /// The object left after removing the listed fields from `e`, printed as an
    /// immediately applied destructuring arrow.
    RecordRest(RestId, Expr),
}

/// Statement node kinds (`J.statement_desc`).
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StmtKind {
    /// A nested block `{ ... }`.
    Block(StmtList),
    /// A variable declaration.
    Variable(VarId),
    /// An expression statement.
    Exp(Expr),
    /// `if (c) { then } else { else }`; an empty else block is not printed.
    If(Expr, StmtList, StmtList),
    /// The optional label is attached when a nested switch emits a labeled
    /// `break`/`continue` targeting this loop.
    While(Option<StrId>, Expr, StmtList),
    /// A `for` loop over an integer range.
    ForRange(ForRangeId),
    /// A `for (x of iterable)` loop.
    ForOf(ForOfId),
    /// A `for await (x of iterable)` loop.
    ForAwaitOf(ForOfId),
    /// `continue`, optionally to a label.
    Continue(Option<StrId>),
    /// `break`, optionally to a label.
    Break(Option<StrId>),
    /// `return e`.
    Return(Expr),
    /// A `switch` over integer cases.
    IntSwitch(Expr, IntSwitchId),
    /// A `switch` over string (and other literal) cases.
    StringSwitch(Expr, StringSwitchId),
    /// `throw e`.
    Throw(Expr),
    /// A `try` statement.
    Try(TryId),
    /// `debugger`.
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
    /// A comment printed before the node.
    pub comment: Option<StrId>,
    /// The source location used for source maps.
    pub source_loc: Option<LamLoc>,
}

/// Function expression header (`J.Fun`). The printer computes the captured
/// identifiers (OCaml's `Js_fun_env`) from the body.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct FunInfo {
    /// Whether the function is a method that may use `this`, printed with `function`.
    pub is_method: bool,
    /// The parameters.
    pub params: IdentList,
    /// The function body.
    pub body: StmtList,
    /// Whether the function returns `unit`.
    pub return_unit: bool,
    /// Whether the function is `async`.
    pub async_: bool,
    /// A directive string printed at the top of the body.
    pub directive: Option<StrId>,
}

/// Variable declaration (`J.variable_declaration`).
#[derive(Debug, Clone)]
pub struct VarDecl {
    /// The declared identifier.
    pub ident: Ident,
    /// The initialiser; `None` declares without a value.
    pub value: Option<Expr>,
    /// The Lambda binding kind (strict, alias, optional or mutable variable).
    pub property: Property,
    /// Usage information set by the dead-code pass.
    pub ident_info: IdentInfo,
}

/// An integer-range `for` loop (`J.ForRange`).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ForRangeInfo {
    /// The loop label, when a nested switch breaks or continues to it.
    pub label: Option<StrId>,
    /// The start value; `None` when the loop variable is already declared.
    pub init: Option<Expr>,
    /// The inclusive bound.
    pub end: Expr,
    /// The loop variable.
    pub ident: IdentId,
    /// Whether the loop counts up or down.
    pub direction: ForDirection,
    /// The loop body.
    pub body: StmtList,
}

/// A `for...of` or `for await...of` loop.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ForOfInfo {
    /// The loop label, when a nested switch breaks or continues to it.
    pub label: Option<StrId>,
    /// The variable bound to each element.
    pub ident: IdentId,
    /// The iterated expression.
    pub iterable: Expr,
    /// The loop body.
    pub body: StmtList,
}

/// Switch case clause (`J.case_clause`).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Clause {
    /// The statements of the case.
    pub body: StmtList,
    /// Whether a `break` follows the body.
    pub should_break: bool,
    /// A comment attached to the `case` label.
    pub comment: Option<StrId>,
    /// The source location used for source maps.
    pub source_loc: Option<LamLoc>,
}

/// A case of a string switch, keyed by any variant-tag literal.
#[derive(Debug, Clone)]
pub struct StringClauseInfo {
    /// The literal the case matches.
    pub tag_type: SwitchCaseTag,
    /// The case body.
    pub clause: Clause,
}

/// The cases of an integer `switch` (`J.Int_switch`).
#[derive(Debug, Clone)]
pub struct IntSwitchInfo {
    /// The cases in order, each with its integer label.
    pub clauses: Vec<(i32, Clause)>,
    /// The `default` case, if any.
    pub default: Option<StmtList>,
}

/// The cases of a string `switch` (`J.String_switch`).
#[derive(Debug, Clone)]
pub struct StringSwitchInfo {
    /// The cases in order.
    pub clauses: Vec<StringClauseInfo>,
    /// The `default` case, if any.
    pub default: Option<StmtList>,
}

/// A `try` statement (`J.Try`).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TryInfo {
    /// The protected block.
    pub body: StmtList,
    /// The `catch` binding and handler, if any.
    pub catch: Option<(IdentId, StmtList)>,
    /// The `finally` block, if any.
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
    /// An empty arena, with slot 0 of every table reserved and the shared empty lists.
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

    /// The kind of expression `e`.
    #[inline]
    pub fn ek(&self, e: Expr) -> ExprKind {
        self.exprs.get(e.index()).kind
    }

    /// The comment and source location of `e`.
    #[inline]
    pub fn expr_cold(&self, e: Expr) -> Cold {
        self.cold(self.exprs.get(e.index()).cold)
    }

    /// The comment of `e`, if any.
    pub fn expr_comment(&self, e: Expr) -> Option<&str> {
        self.expr_cold(e).comment.map(|s| self.text(s))
    }

    /// The source location of `e`, if any.
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

    /// Push a statement without comment or location.
    #[inline]
    pub fn stmt(&mut self, kind: StmtKind) -> Stmt {
        Stmt::new(self.stmts.push(StmtNode { kind, cold: None }))
    }

    /// Push a statement with the given cold data.
    pub fn stmt_with(&mut self, kind: StmtKind, cold: Cold) -> Stmt {
        let cold = self.cold_of(cold.comment, cold.source_loc);
        Stmt::new(self.stmts.push(StmtNode { kind, cold }))
    }

    /// The kind of statement `s`.
    #[inline]
    pub fn sk(&self, s: Stmt) -> StmtKind {
        self.stmts.get(s.index()).kind
    }

    /// The comment and source location of `s`.
    #[inline]
    pub fn stmt_cold(&self, s: Stmt) -> Cold {
        self.cold(self.stmts.get(s.index()).cold)
    }

    /// The comment of `s`, if any.
    pub fn stmt_comment(&self, s: Stmt) -> Option<&str> {
        self.stmt_cold(s).comment.map(|c| self.text(c))
    }

    /// The source location of `s`, if any.
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

    /// `s` with replaced cold data; `s` itself when the data is unchanged.
    pub fn with_stmt_cold(&mut self, s: Stmt, cold: Cold) -> Stmt {
        let node = *self.stmts.get(s.index());
        if self.cold(node.cold) == cold {
            return s;
        }
        self.stmt_with(node.kind, cold)
    }

    /// `s` with its comment replaced.
    pub fn with_stmt_comment(&mut self, s: Stmt, comment: Option<&str>) -> Stmt {
        let mut cold = self.stmt_cold(s);
        cold.comment = comment.map(|c| self.str(c));
        self.with_stmt_cold(s, cold)
    }

    /// `s` with its source location replaced.
    pub fn with_stmt_loc(&mut self, s: Stmt, source_loc: Option<LamLoc>) -> Stmt {
        let mut cold = self.stmt_cold(s);
        cold.source_loc = source_loc;
        self.with_stmt_cold(s, cold)
    }

    // ---- lists -----------------------------------------------------------

    /// Intern `items` as an expression list.
    pub fn expr_list(&mut self, items: &[Expr]) -> ExprList {
        ExprList::new(self.expr_lists.push_slice(items))
    }

    /// Intern the items of an iterator as an expression list.
    pub fn expr_list_from(&mut self, items: impl IntoIterator<Item = Expr>) -> ExprList {
        ExprList::new(self.expr_lists.push_iter(items))
    }

    /// The items of an expression list.
    #[inline]
    pub fn exprs(&self, list: ExprList) -> &[Expr] {
        self.expr_lists.get(list.index())
    }

    /// Intern `items` as a block.
    pub fn stmt_list(&mut self, items: &[Stmt]) -> StmtList {
        StmtList::new(self.stmt_lists.push_slice(items))
    }

    /// Intern the items of an iterator as a block.
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

    /// The statements of a block.
    #[inline]
    pub fn stmts(&self, list: StmtList) -> &[Stmt] {
        self.stmt_lists.get(list.index())
    }

    /// An owned copy of a block's statement handles, for passes that rebuild
    /// the block.
    pub fn block_vec(&self, list: StmtList) -> Vec<Stmt> {
        self.stmts(list).to_vec()
    }

    /// An owned copy of an expression list's handles.
    pub fn expr_vec(&self, list: ExprList) -> Vec<Expr> {
        self.exprs(list).to_vec()
    }

    /// The current top of the expression scratch stack.
    #[inline]
    pub fn expr_scratch_mark(&self) -> usize {
        self.expr_scratch.len()
    }

    /// Push `e` onto the expression scratch stack.
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

    /// Pop the expression scratch stack back to `mark` without building a list.
    #[inline]
    pub fn expr_scratch_truncate(&mut self, mark: usize) {
        self.expr_scratch.truncate(mark);
    }

    /// The current top of the statement scratch stack.
    #[inline]
    pub fn stmt_scratch_mark(&self) -> usize {
        self.stmt_scratch.len()
    }

    /// Push `s` onto the statement scratch stack.
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

    /// Pop the statement scratch stack back to `mark` without building a block.
    #[inline]
    pub fn stmt_scratch_truncate(&mut self, mark: usize) {
        self.stmt_scratch.truncate(mark);
    }

    /// Intern `items` as an object-literal property list.
    pub fn prop_list(&mut self, items: &[(PropName, Expr)]) -> PropList {
        PropList::new(self.prop_lists.push_slice(items))
    }

    /// Intern the items of an iterator as an object-literal property list.
    pub fn prop_list_from(
        &mut self,
        items: impl IntoIterator<Item = (PropName, Expr)>,
    ) -> PropList {
        PropList::new(self.prop_lists.push_iter(items))
    }

    /// The entries of a property list.
    #[inline]
    pub fn props(&self, list: PropList) -> &[(PropName, Expr)] {
        self.prop_lists.get(list.index())
    }

    /// Intern `items` as an identifier list.
    pub fn ident_list(&mut self, items: &[Ident]) -> IdentList {
        IdentList::new(self.ident_lists.push_slice(items))
    }

    /// The identifiers of an identifier list.
    #[inline]
    pub fn ident_slice(&self, list: IdentList) -> &[Ident] {
        self.ident_lists.get(list.index())
    }

    // ---- strings ---------------------------------------------------------

    /// Store `s` in the text buffer. Strings are not deduplicated.
    pub fn str(&mut self, s: &str) -> StrId {
        let start = checked_u32(self.text.len());
        self.text.push_str(s);
        StrId::new(self.strs.push(Span {
            start,
            len: checked_u32(s.len()),
        }))
    }

    /// The text of a stored string.
    #[inline]
    pub fn text(&self, id: StrId) -> &str {
        &self.text[self.strs.get(id.index()).range()]
    }

    /// The text of a literal property name; `None` for the symbol key.
    pub fn prop_name_text(&self, name: PropName) -> Option<&str> {
        match name {
            PropName::Lit(s) => Some(self.text(s)),
            PropName::Symbol => None,
        }
    }

    // ---- side tables -----------------------------------------------------

    /// An upper bound for fresh identifiers, scanning the identifier payload
    /// tables rather than recursively visiting the program. Eliminated nodes
    /// may contribute stamps too; they cannot cause a collision.
    pub(crate) fn ident_stamp_bound(&self) -> i32 {
        self.idents
            .rows
            .iter()
            .chain(&self.ident_lists.items)
            .map(Ident::stamp)
            .chain(self.vars.rows.iter().map(|decl| decl.ident.stamp()))
            .chain(self.quals.rows.iter().map(|(module, _)| module.id.stamp()))
            .chain(
                self.rests
                    .rows
                    .iter()
                    .flatten()
                    .filter_map(|field| field.ident.map(|id| id.stamp())),
            )
            .max()
            .unwrap_or(0)
            .max(0)
    }

    /// Store an identifier.
    pub fn ident_id(&mut self, id: Ident) -> IdentId {
        IdentId::new(self.idents.push(id))
    }

    /// A stored identifier.
    #[inline]
    pub fn ident(&self, id: IdentId) -> Ident {
        *self.idents.get(id.index())
    }

    /// Store a number literal.
    pub fn number_id(&mut self, n: Number) -> NumId {
        NumId::new(self.numbers.push(n))
    }

    /// A stored number literal.
    #[inline]
    pub fn number(&self, id: NumId) -> &Number {
        self.numbers.get(id.index())
    }

    /// Store call metadata.
    pub fn call_id(&mut self, info: CallInfo) -> CallId {
        CallId::new(self.calls.push(info))
    }

    /// Stored call metadata.
    #[inline]
    pub fn call_info(&self, id: CallId) -> &CallInfo {
        self.calls.get(id.index())
    }

    /// Store a function header.
    pub fn fun_id(&mut self, info: FunInfo) -> FunId {
        FunId::new(self.funs.push(info))
    }

    /// A stored function header.
    #[inline]
    pub fn fun(&self, id: FunId) -> FunInfo {
        *self.funs.get(id.index())
    }

    /// Store block tag info.
    pub fn tag_id(&mut self, tag: TagInfo) -> TagId {
        TagId::new(self.tags.push(tag))
    }

    /// Stored block tag info.
    #[inline]
    pub fn tag(&self, id: TagId) -> &TagInfo {
        self.tags.get(id.index())
    }

    /// Store a module reference with an optional member name.
    pub fn qual_id(&mut self, module: ModuleId, member: Option<String>) -> QualId {
        QualId::new(self.quals.push((module, member)))
    }

    /// A stored module reference and member name.
    #[inline]
    pub fn qual(&self, id: QualId) -> (&ModuleId, Option<&str>) {
        let (module, member) = self.quals.get(id.index());
        (module, member.as_deref())
    }

    /// Store raw JavaScript code.
    pub fn raw_id(&mut self, info: JsRawInfo) -> RawId {
        RawId::new(self.raws.push(info))
    }

    /// Stored raw JavaScript code.
    #[inline]
    pub fn raw(&self, id: RawId) -> &JsRawInfo {
        self.raws.get(id.index())
    }

    /// Store the segment of a non-interpolated template literal.
    pub fn template_id(&mut self, segment: crate::string_literal::TemplateSegment) -> TemplateId {
        TemplateId::new(self.templates.push(segment))
    }

    /// A stored template literal segment.
    #[inline]
    pub fn template(&self, id: TemplateId) -> &crate::string_literal::TemplateSegment {
        self.templates.get(id.index())
    }

    /// Store the segments of an interpolated template literal.
    pub fn segments_id(
        &mut self,
        segments: Vec<crate::string_literal::TemplateSegment>,
    ) -> SegmentsId {
        SegmentsId::new(self.segments.push(segments))
    }

    /// Stored interpolated template segments.
    #[inline]
    pub fn segments(&self, id: SegmentsId) -> &[crate::string_literal::TemplateSegment] {
        self.segments.get(id.index())
    }

    /// Store the raw string segments of a tagged template.
    pub fn tagged_id(&mut self, strings: Vec<String>) -> TaggedId {
        TaggedId::new(self.tagged.push(strings))
    }

    /// Stored tagged template segments.
    #[inline]
    pub fn tagged(&self, id: TaggedId) -> &[String] {
        self.tagged.get(id.index())
    }

    /// Store the fields excluded by an object-rest expression.
    pub fn rest_id(&mut self, fields: Vec<RecordRestField>) -> RestId {
        RestId::new(self.rests.push(fields))
    }

    /// Stored object-rest fields.
    #[inline]
    pub fn rest(&self, id: RestId) -> &[RecordRestField] {
        self.rests.get(id.index())
    }

    /// Store a variable declaration.
    pub fn var_id(&mut self, decl: VarDecl) -> VarId {
        VarId::new(self.vars.push(decl))
    }

    /// A stored variable declaration.
    #[inline]
    pub fn var(&self, id: VarId) -> &VarDecl {
        self.vars.get(id.index())
    }

    /// The one in-place mutation the IR allows: OCaml's mutable
    /// `ident_info` field.
    pub fn var_ident_info_mut(&mut self, id: VarId) -> &mut IdentInfo {
        &mut self.vars.get_mut(id.index()).ident_info
    }

    /// Store an integer-range `for` loop.
    pub fn for_range_id(&mut self, info: ForRangeInfo) -> ForRangeId {
        ForRangeId::new(self.for_ranges.push(info))
    }

    /// A stored integer-range `for` loop.
    #[inline]
    pub fn for_range(&self, id: ForRangeId) -> ForRangeInfo {
        *self.for_ranges.get(id.index())
    }

    /// Store a `for...of` loop.
    pub fn for_of_id(&mut self, info: ForOfInfo) -> ForOfId {
        ForOfId::new(self.for_ofs.push(info))
    }

    /// A stored `for...of` loop.
    #[inline]
    pub fn for_of(&self, id: ForOfId) -> ForOfInfo {
        *self.for_ofs.get(id.index())
    }

    /// Store the cases of an integer switch.
    pub fn int_switch_id(&mut self, info: IntSwitchInfo) -> IntSwitchId {
        IntSwitchId::new(self.int_switches.push(info))
    }

    /// Stored integer switch cases.
    #[inline]
    pub fn int_switch(&self, id: IntSwitchId) -> &IntSwitchInfo {
        self.int_switches.get(id.index())
    }

    /// Store the cases of a string switch.
    pub fn string_switch_id(&mut self, info: StringSwitchInfo) -> StringSwitchId {
        StringSwitchId::new(self.string_switches.push(info))
    }

    /// Stored string switch cases.
    #[inline]
    pub fn string_switch(&self, id: StringSwitchId) -> &StringSwitchInfo {
        self.string_switches.get(id.index())
    }

    /// Store a `try` statement.
    pub fn try_id(&mut self, info: TryInfo) -> TryId {
        TryId::new(self.tries.push(info))
    }

    /// A stored `try` statement.
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
    /// The arena holding every node of the program.
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
    /// The program itself.
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
    fn stamp_bound_includes_every_identifier_table() {
        let mut a = JsArena::new();
        let id = |stamp| Ident::new("x", stamp, crate::ident::IdentFlags::NONE);
        assert_eq!(a.ident_stamp_bound(), 0);
        a.ident_id(id(10));
        assert_eq!(a.ident_stamp_bound(), 10);
        a.ident_list(&[id(20)]);
        assert_eq!(a.ident_stamp_bound(), 20);
        a.var_id(VarDecl {
            ident: id(30),
            value: None,
            property: Property::Strict,
            ident_info: IdentInfo::default(),
        });
        assert_eq!(a.ident_stamp_bound(), 30);
        a.qual_id(
            ModuleId {
                id: id(40),
                kind: super::super::Kind::Ml,
                dynamic_import: false,
            },
            None,
        );
        assert_eq!(a.ident_stamp_bound(), 40);
        a.rest_id(vec![RecordRestField {
            label: "x".into(),
            ident: Some(id(50)),
        }]);
        assert_eq!(a.ident_stamp_bound(), 50);
    }

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
