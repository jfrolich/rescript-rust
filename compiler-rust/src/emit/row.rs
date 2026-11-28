//! The facts of one JavaScript node (THREE_TREES 11.4, "T6 design" (a) and
//! "T6: the interface" (a)): the flags, the J-level kind and the row. One
//! definition for the builder (`emit/builder.rs`), which writes a row per
//! node, and for the lowering's interface (`bir/lower/js.rs`), which reads
//! kinds and flags through it. Data only: nothing here builds a node.
/// The facts of one node, as bits of [`Row::flags`].
pub mod flag {
    /// B:102 `expression_has_no_side_effects`.
    pub const PURE: u16 = 1 << 0;
    /// E:15 `js_expr_no_side_effects`.
    pub const STRICT: u16 = 1 << 1;
    /// A:28 `delay_safe`.
    pub const DELAY_SAFE: u16 = 1 << 2;
    /// E:146 `is_pure_subexpression`.
    pub const SUBEXPR: u16 = 1 << 3;
    /// X:60 `duplicable`.
    pub const DUPLICABLE: u16 = 1 << 4;
    /// A function literal is at or below this node.
    pub const HAS_FUN: u16 = 1 << 5;
    /// The seal has work at or below this node: a logical or `|` chain or a
    /// sequence that is not in print form, or a function literal whose body
    /// the flatten rules change.
    pub const SEAL: u16 = 1 << 6;
    /// A JSX element printed as JSX is at or below this node: the seal
    /// writes its indentation (THREE_TREES 11.4, "T6: the interface" (e)).
    pub const JSX: u16 = 1 << 7;
    /// A reference to a JavaScript global is at or below this node: the
    /// replay's walk decides whether it prints as `globalThis.name` ((d)).
    pub const HAS_GLOBAL: u16 = 1 << 8;
}

/// What the caller knows of a variable when it builds a reference to it.
pub mod var {
    /// The variable is assigned after its declaration.
    pub const ASSIGNED: u8 = 1 << 0;
    /// A JavaScript global.
    pub const GLOBAL: u8 = 1 << 1;
}

/// [`Row::aux`] of a [`Kind::Number`].
pub mod num {
    /// The class, in the low two bits: an integer.
    pub const INT: u8 = 0;
    /// A float.
    pub const FLOAT: u8 = 1;
    /// A bigint.
    pub const BIGINT: u8 = 2;
    /// The mask of the class.
    pub const CLASS: u8 = 3;
    /// An integer that is not zero; a bigint whose digits are not `0`.
    pub const NONZERO: u8 = 1 << 2;
    /// A bigint with the positive sign.
    pub const POSITIVE: u8 = 1 << 3;
}

/// The J-level kind of a node: what the lowering built, which the oxc node
/// alone does not say (a length is a member, a string append is a `+`).
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// A reference to a variable; `payload` is the variable's index, `aux`
    /// what the caller knew of it ([`var`]).
    Var,
    /// An identifier printed as written; `aux` is 1 for a JavaScript
    /// identifier.
    Named,
    /// `aux` is of [`num`]; `payload` is an integer's value.
    Number,
    /// A string literal.
    Str,
    /// `aux` is the value.
    Bool,
    /// `null`.
    Null,
    /// `aux` is 1 for the unit value.
    Undefined,
    /// `aux` is the `BinOp`.
    Bin,
    /// `!value`.
    Not,
    /// `~value`.
    Bnot,
    /// `typeof value`.
    Typeof,
    /// `left in right`.
    In,
    /// `test ? yes : no`.
    Cond,
    /// `first, second`.
    Seq,
    /// `payload` is the call information of the lowering.
    Call,
    /// `new callee(arguments)`.
    New,
    /// `object[index]`.
    Index,
    /// `payload` is the field position plus one, 0 for none; `aux` is 1 for
    /// the tag of a block.
    Dot,
    /// The length of a string, an array, a function or bytes.
    Length,
    /// `value == null`.
    IsNullish,
    /// A string append, printed as `+`.
    StrAppend,
    /// Statements (T6b). An expression statement.
    Exp,
    /// `return value`.
    Return,
    /// `throw value`.
    Throw,
    /// `payload` is the variable's index; `aux` is the `LetKind` in its low
    /// two bits and the `UsedStats` of the declaration above them.
    Declare,
    /// `if`, with both blocks.
    If,
    /// A block statement.
    Block,
    /// `while`.
    While,
    /// `break`.
    Break,
    /// `continue`.
    Continue,
    /// `debugger`.
    Debugger,
    /// The kinds below were added by the design of the lowering's interface
    /// (THREE_TREES 11.4, "T6: the interface"), which reads them before a
    /// constructor of the builder exists for them. Expressions first.
    /// A function literal; `payload` is the `FuncId` of its header.
    Fun,
    /// An object literal; `payload` is the `JsId` of its keys.
    Object,
    /// An array literal; `aux` is 0 immutable, 1 mutable, 2 unknown.
    Array,
    /// A block literal; `payload` is the `JsId` of its tag information,
    /// `aux` as for `Array`.
    BlockLit,
    /// `Some(value)`; `aux` is 1 when it prints as its value.
    Optional,
    /// `payload` is the `JsId` of the element's header; `aux` is 1 when it
    /// has a children list.
    Jsx,
    /// A template literal; `payload` is the `JsId` of its parts, `aux` is
    /// 1 for a literal without interpolation.
    Template,
    /// A tagged template; `payload` as for `Template`.
    Tagged,
    /// Raw JavaScript; `payload` is the `StrId` of its text, `aux` is 1
    /// for a statement.
    Raw,
    /// `await value`.
    Await,
    /// `...value`.
    Spread,
    /// An imported module, or a member of one; `payload` is the
    /// `ImportId`.
    Qualified,
    /// `payload` is the `StrId` of the text.
    Json,
    /// `payload` is the `JsId` of the rest descriptor.
    RecordRest,
    /// A call whose arguments are one array expression.
    FlatCall,
    /// Statements. A range loop over a new variable; `payload` is the
    /// variable's index.
    ForRange,
    /// A range loop over an existing variable.
    ForRangeExisting,
    /// `payload` is the variable's index.
    ForOf,
    /// `for await (... of ...)`; `payload` is the variable's index.
    ForAwaitOf,
    /// `aux` is 0 for an integer switch, 1 for a string switch; `payload`
    /// is the `SwitchId`.
    Switch,
    /// `try`; `payload` is the index of the exception variable plus one,
    /// 0 without a handler.
    Try,
    /// A declaration by a rest pattern; `payload` is the variable's index,
    /// `aux` as for `Declare`.
    Rest,
}

impl Kind {
    /// Every kind, in the order of its number.
    pub const ALL: [Kind; 53] = [
        Kind::Var,
        Kind::Named,
        Kind::Number,
        Kind::Str,
        Kind::Bool,
        Kind::Null,
        Kind::Undefined,
        Kind::Bin,
        Kind::Not,
        Kind::Bnot,
        Kind::Typeof,
        Kind::In,
        Kind::Cond,
        Kind::Seq,
        Kind::Call,
        Kind::New,
        Kind::Index,
        Kind::Dot,
        Kind::Length,
        Kind::IsNullish,
        Kind::StrAppend,
        Kind::Exp,
        Kind::Return,
        Kind::Throw,
        Kind::Declare,
        Kind::If,
        Kind::Block,
        Kind::While,
        Kind::Break,
        Kind::Continue,
        Kind::Debugger,
        Kind::Fun,
        Kind::Object,
        Kind::Array,
        Kind::BlockLit,
        Kind::Optional,
        Kind::Jsx,
        Kind::Template,
        Kind::Tagged,
        Kind::Raw,
        Kind::Await,
        Kind::Spread,
        Kind::Qualified,
        Kind::Json,
        Kind::RecordRest,
        Kind::FlatCall,
        Kind::ForRange,
        Kind::ForRangeExisting,
        Kind::ForOf,
        Kind::ForAwaitOf,
        Kind::Switch,
        Kind::Try,
        Kind::Rest,
    ];
}

/// The facts of one node. 8 bytes: one per node in `Builder::rows` (`emit/builder.rs`), and
/// the same value travels in the handle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Row {
    /// Bits of [`flag`].
    pub flags: u16,
    /// What the node is.
    pub kind: Kind,
    /// As [`Kind`] says for the kind.
    pub aux: u8,
    /// As [`Kind`] says for the kind.
    pub payload: u32,
}

impl Row {
    /// O(1).
    pub fn has(self, flags: u16) -> bool {
        self.flags & flags == flags
    }
    /// O(1): the value of an integer literal.
    pub fn int(self) -> Option<i32> {
        (self.kind == Kind::Number && self.aux & num::CLASS == num::INT)
            .then_some(self.payload as i32)
    }
}
