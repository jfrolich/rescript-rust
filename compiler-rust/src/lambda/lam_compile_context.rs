//! Lambda compilation context.
//!
//! This module provides the compilation context used when transforming
//! Lambda IR to JavaScript IR. It tracks continuation, exception handlers,
//! and compilation metadata.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use ahash::{AHashMap as HashMap, AHashSet as HashSet};

use crate::ident::Ident;
use crate::lambda::Lambda;
use crate::lambda::lam_arity::Arity;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_constant::Constant;

/// Label for jump tables (exception handler labels).
pub type JblLabel = i32;

/// Recursion flag for functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum RecFlag {
    /// Recursive function
    Rec,
    /// Non-recursive function
    NonRec,
    /// Self-recursive function (special case)
    SelfRec,
}

/// Element in a block.
#[derive(Debug, Clone)]
#[allow(clippy::large_enum_variant)]
pub enum Element {
    /// No information available
    Na,
    /// Simple form - can be substituted
    SimpleForm(Lambda),
}

/// Nullable kind for optional values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoxedNullable {
    Undefined,
    Null,
    NullUndefined,
}

/// Information about an identifier's kind.
///
/// This tracks what kind of value an identifier is bound to,
/// which helps with optimization and code generation.
#[derive(Debug, Clone, Default)]
pub enum IdKind {
    /// Optional value with normal null handling
    NormalOptional(Lambda),
    /// Optional block with nullable kind
    OptionalBlock(Lambda, BoxedNullable),
    /// Immutable block (tuple, record)
    ImmutableBlock(Vec<Element>),
    /// Mutable block
    MutableBlock(Vec<Element>),
    /// Constant value
    Constant(Constant),
    /// Module reference
    Module(Ident),
    /// Function with arity information
    FunctionId {
        arity: Arity,
        lambda: Option<(Lambda, RecFlag)>,
    },
    /// Exception identifier
    Exception,
    /// Function parameter
    Parameter,
    /// No specific information (default)
    #[default]
    Na,
}

/// Identifier table for tracking identifier kinds.
pub type IdentTable = HashMap<Ident, IdKind>;

#[derive(Debug, Clone)]
pub enum ExternalArityInfo {
    Single(Arity),
    Submodule(Vec<Arity>),
}

pub type ExternalArityFieldTable = HashMap<String, Option<ExternalArityInfo>>;

/// `Lam_compile_env.query_external_id_info` results, per module and field.
pub type ExternalArityTable = HashMap<String, ExternalArityFieldTable>;

/// Lambda compilation statistics and metadata.
#[derive(Debug, Clone)]
pub struct LamStats {
    /// Set of export identifiers
    pub export_idents: HashSet<Ident>,
    /// List of exports (in order)
    pub exports: Vec<Ident>,
    /// Identifier kind table
    pub ident_tbl: IdentTable,
    /// Arity metadata loaded from dependency `.cmj` entries.
    ///
    /// OCaml's `Lam_arity_analysis.get_arity` queries
    /// `Lam_compile_env.query_external_id_info` directly
    /// (compiler/core/lam_arity_analysis.ml:43-71). Rust keeps the resolved
    /// metadata here so the later collect/alpha passes can consult it without
    /// probing the filesystem themselves.
    pub external_arities: ExternalArityTable,
    /// Shared stamp counter for `Ident::rename` calls across the pipeline.
    ///
    /// OCaml's `Ident.rename` consults a single global mutable counter, so every
    /// freshly-renamed ident gets a stamp unused anywhere else. The Rust pipeline
    /// previously created a new `IdGenerator::with_start_stamp(max_ident_stamp(..))`
    /// inside each beta-reduce call, which made two inlinings of the same function
    /// produce colliding stamps (e.g. two `let prim` bindings at module top level
    /// in `coercion_module_alias_test`). Threading this shared counter through the
    /// simplify pipeline preserves OCaml's invariant.
    pub id_gen: std::sync::Arc<crate::context::IdGenerator>,
    /// Whether collect stores inlinable function bodies in `FunctionId`.
    /// Only `remove_alias` reads them, so a collect whose table is fully
    /// re-collected before the next `simplify_alias` can skip the copies.
    pub(crate) collect_function_payloads: bool,
}

impl LamStats {
    /// Create a new LamStats with the given exports.
    pub fn new(exports: Vec<Ident>) -> Self {
        let export_idents: HashSet<Ident> = exports.iter().cloned().collect();
        Self {
            export_idents,
            exports,
            ident_tbl: HashMap::new(),
            external_arities: ExternalArityTable::default(),
            id_gen: std::sync::Arc::new(crate::context::IdGenerator::new()),
            collect_function_payloads: true,
        }
    }

    /// Check if an identifier is exported.
    pub fn is_export(&self, id: &Ident) -> bool {
        self.export_idents.contains(id)
    }

    /// Get the kind of an identifier.
    pub fn get_kind(&self, id: &Ident) -> Option<&IdKind> {
        self.ident_tbl.get(id)
    }

    /// Set the kind of an identifier.
    pub fn set_kind(&mut self, id: Ident, kind: IdKind) {
        self.ident_tbl.insert(id, kind);
    }
}

/// Return label for tail call optimization.
#[derive(Debug, Clone)]
pub struct ReturnLabel {
    /// Identifier for the return label
    pub id: Ident,
    /// Parameters for the return
    pub params: Vec<Ident>,
    /// Mask indicating which parameters are immutable
    pub immutable_mask: Vec<bool>,
    /// New parameter mappings (for renaming)
    pub new_params: HashMap<Ident, Ident>,
    /// Whether this label has been triggered
    pub triggered: bool,
}

impl ReturnLabel {
    /// Create a new return label.
    pub fn new(id: Ident, params: Vec<Ident>, immutable_mask: Vec<bool>) -> Self {
        Self {
            id,
            params,
            immutable_mask,
            new_params: HashMap::new(),
            triggered: false,
        }
    }
}

/// Tail position information.
#[derive(Debug, Clone)]
pub struct Tail {
    /// Optional return label for tail calls
    pub label: Option<ReturnLabel>,
    /// Whether we're inside a staticcatch
    pub in_staticcatch: bool,
}

impl Tail {
    /// Create a new tail position info.
    pub fn new(label: Option<ReturnLabel>, in_staticcatch: bool) -> Self {
        Self {
            label,
            in_staticcatch,
        }
    }

    /// Create tail info with no label.
    pub fn none() -> Self {
        Self {
            label: None,
            in_staticcatch: false,
        }
    }
}

/// Maybe tail - for exception handling context.
#[derive(Debug, Clone)]
pub enum MaybeTail {
    /// In a try block (not real tail position)
    TailInTry,
    /// With tail information
    TailWithName(Tail),
}

/// Tail type - whether we're in tail position.
#[derive(Debug, Clone)]
pub enum TailType {
    /// Not in tail position
    NotTail,
    /// Maybe in tail position (with context)
    MaybeTailIsReturn(MaybeTail),
}

impl TailType {
    /// Check if this might be a return position.
    pub fn is_maybe_return(&self) -> bool {
        matches!(self, TailType::MaybeTailIsReturn(_))
    }
}

/// Continuation - what to do with the result of an expression.
#[derive(Debug, Clone)]
pub enum Continuation {
    /// Expression is called for effect only
    EffectCall(TailType),
    /// Expression result is needed as a value
    NeedValue(TailType),
    /// Declare a new variable with the result
    Declare(LetKind, Ident),
    /// Assign the result to an existing variable
    Assign(Ident),
}

impl Continuation {
    /// Check if this continuation is a return.
    pub fn is_return(&self) -> bool {
        match self {
            Continuation::EffectCall(tt) | Continuation::NeedValue(tt) => tt.is_maybe_return(),
            Continuation::Declare(_, _) | Continuation::Assign(_) => false,
        }
    }
}

/// Value for jump table entries.
#[derive(Debug, Clone)]
pub struct JmpValue {
    /// Exit identifier
    pub exit_id: Ident,
    /// Bindings for this handler
    pub bindings: Vec<Ident>,
    /// Order ID for sorting
    pub order_id: i32,
}

/// Jump table - maps exception labels to handler info.
pub type JmpTable = HashMap<JblLabel, JmpValue>;

/// Exception handler definition.
#[derive(Debug, Clone)]
pub struct Handler {
    /// Handler label
    pub label: JblLabel,
    /// Handler body
    pub handler: Lambda,
    /// Bindings for this handler
    pub bindings: Vec<Ident>,
}

/// Frame describing one enclosing loop. The label is allocated lazily via
/// [`CompileContext::ensure_loop_label`] when a nested switch needs to
/// emit a labeled `break`/`continue`. Mirrors OCaml's
/// `Lam_compile_context.loop_frame`.
#[derive(Debug, Clone, Default)]
pub struct LoopFrame {
    label: Rc<RefCell<Option<String>>>,
}

impl LoopFrame {
    /// Get the currently-attached JS label for this loop, if any.
    pub fn label(&self) -> Option<String> {
        self.label.borrow().clone()
    }

    /// Attach a JS label to this frame (used by
    /// `LambdaCompiler::ensure_loop_label`).
    pub fn set_label(&self, label: String) {
        *self.label.borrow_mut() = Some(label);
    }
}

/// Lambda compilation context.
///
/// This is the main context used during Lambda to JS IR compilation.
/// It tracks the current continuation, exception handlers, and metadata.
#[derive(Debug, Clone)]
pub struct CompileContext {
    /// Current continuation
    pub continuation: Continuation,
    /// Jump table for exception handlers
    pub jmp_table: JmpTable,
    /// Compilation metadata
    pub meta: LamStats,
    /// Number of enclosing JS `switch` statements between the current
    /// expression and the closest enclosing loop. Mirrors OCaml's
    /// `switch_depth` field. Bumped by [`CompileContext::enter_switch`]
    /// when compiling switch arms.
    pub switch_depth: i32,
    /// Stack of enclosing loops, innermost first. Mirrors OCaml's
    /// `loop_stack` field. Pushed by [`CompileContext::push_loop`] when
    /// compiling `Lwhile`/`Lfor` bodies.
    pub loop_stack: Vec<LoopFrame>,
    /// Counter shared across the whole compilation unit, used to mint
    /// unique JS labels (`loop_0`, `loop_1`, ...) when nested switches
    /// need labeled break/continue. Mirrors OCaml's
    /// `loop_label_counter`.
    pub loop_label_counter: Rc<Cell<i32>>,
}

impl CompileContext {
    /// Create a new compilation context.
    pub fn new(continuation: Continuation, meta: LamStats) -> Self {
        Self {
            continuation,
            jmp_table: HashMap::new(),
            meta,
            switch_depth: 0,
            loop_stack: Vec::new(),
            loop_label_counter: Rc::new(Cell::new(0)),
        }
    }

    /// Create a context for effect-only compilation.
    pub fn effect_call(meta: LamStats) -> Self {
        Self::new(Continuation::EffectCall(TailType::NotTail), meta)
    }

    /// Create a context for value-needed compilation.
    pub fn need_value(meta: LamStats) -> Self {
        Self::new(Continuation::NeedValue(TailType::NotTail), meta)
    }

    /// Bump `switch_depth`. Mirrors OCaml's `enter_switch`.
    pub fn enter_switch(&self) -> Self {
        let mut next = self.clone();
        next.switch_depth += 1;
        next
    }

    /// Push a fresh loop frame onto `loop_stack` and return both the
    /// new context and the frame handle (so callers can read back the
    /// lazily-attached label after compiling the body). Mirrors OCaml's
    /// `push_loop`.
    pub fn push_loop(&self) -> (Self, LoopFrame) {
        let frame = LoopFrame::default();
        let mut next = self.clone();
        next.loop_stack.insert(0, frame.clone());
        (next, frame)
    }

    /// Allocate a JS label for `frame` if it does not already have one,
    /// then return it. Mirrors OCaml's `ensure_loop_label`.
    pub fn ensure_loop_label(&self, frame: &LoopFrame) -> String {
        let mut slot = frame.label.borrow_mut();
        if let Some(existing) = slot.as_ref() {
            return existing.clone();
        }
        let next_id = self.loop_label_counter.get();
        self.loop_label_counter.set(next_id + 1);
        let label = format!("loop_{next_id}");
        *slot = Some(label.clone());
        label
    }

    /// Innermost enclosing loop frame, if any.
    pub fn current_loop_frame(&self) -> Option<&LoopFrame> {
        self.loop_stack.first()
    }

    /// Find a handler by label.
    pub fn find_handler(&self, label: JblLabel) -> Option<&JmpValue> {
        self.jmp_table.get(&label)
    }

    /// Add handlers to the jump table.
    ///
    /// Returns the updated jump table and a list of (order_id, handler) pairs.
    pub fn add_handlers(&mut self, exit_id: Ident, handlers: Vec<Handler>) -> Vec<(i32, Lambda)> {
        let base_order = self.jmp_table.len() as i32 + 1;
        let mut result = Vec::new();

        for (i, h) in handlers.into_iter().enumerate() {
            let order_id = base_order + i as i32;
            self.jmp_table.insert(
                h.label,
                JmpValue {
                    exit_id,
                    bindings: h.bindings,
                    order_id,
                },
            );
            result.push((order_id, h.handler));
        }

        result
    }

    /// Add a pseudo handler (for simplified cases).
    pub fn add_pseudo_handler(&mut self, exit_id: Ident, handler: Handler) -> Lambda {
        self.jmp_table.insert(
            handler.label,
            JmpValue {
                exit_id,
                bindings: handler.bindings,
                order_id: -1,
            },
        );
        handler.handler
    }

    /// Check if the continuation is a return.
    pub fn is_return(&self) -> bool {
        self.continuation.is_return()
    }

    /// Create a new context with a different continuation.
    pub fn with_continuation(&self, continuation: Continuation) -> Self {
        let mut next = self.clone();
        next.continuation = continuation;
        next
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lam_stats_creation() {
        let x = Ident::create_local("x");
        let y = Ident::create_local("y");
        let stats = LamStats::new(vec![x, y]);

        assert!(stats.is_export(&x));
        assert!(stats.is_export(&y));
        assert!(!stats.is_export(&Ident::create_local("z")));
    }

    #[test]
    fn test_id_kind() {
        let x = Ident::create_local("x");
        let mut stats = LamStats::new(vec![]);

        stats.set_kind(x, IdKind::Parameter);
        assert!(matches!(stats.get_kind(&x), Some(IdKind::Parameter)));

        stats.set_kind(
            x,
            IdKind::FunctionId {
                arity: Arity::info(vec![2], false),
                lambda: None,
            },
        );
        assert!(matches!(
            stats.get_kind(&x),
            Some(IdKind::FunctionId { .. })
        ));
    }

    #[test]
    fn test_continuation_is_return() {
        let effect_not_tail = Continuation::EffectCall(TailType::NotTail);
        assert!(!effect_not_tail.is_return());

        let effect_maybe = Continuation::EffectCall(TailType::MaybeTailIsReturn(
            MaybeTail::TailWithName(Tail::none()),
        ));
        assert!(effect_maybe.is_return());

        let declare = Continuation::Declare(LetKind::Strict, Ident::create_local("x"));
        assert!(!declare.is_return());
    }

    #[test]
    fn test_compile_context_creation() {
        let stats = LamStats::new(vec![]);
        let ctx = CompileContext::effect_call(stats.clone());

        assert!(matches!(
            ctx.continuation,
            Continuation::EffectCall(TailType::NotTail)
        ));
        assert!(ctx.jmp_table.is_empty());

        let ctx = CompileContext::need_value(stats);
        assert!(matches!(
            ctx.continuation,
            Continuation::NeedValue(TailType::NotTail)
        ));
    }

    #[test]
    fn test_add_handlers() {
        let stats = LamStats::new(vec![]);
        let mut ctx = CompileContext::effect_call(stats);

        let exit_id = Ident::create_local("exit");
        let x = Ident::create_local("x");

        let handlers = vec![
            Handler {
                label: 1,
                handler: Lambda::unit(),
                bindings: vec![x],
            },
            Handler {
                label: 2,
                handler: Lambda::true_(),
                bindings: vec![],
            },
        ];

        let result = ctx.add_handlers(exit_id, handlers);

        assert_eq!(result.len(), 2);
        assert_eq!(ctx.jmp_table.len(), 2);

        let h1 = ctx.find_handler(1).unwrap();
        assert_eq!(h1.exit_id, exit_id);
        assert_eq!(h1.bindings.len(), 1);
        assert!(h1.order_id > 0);
    }

    #[test]
    fn test_with_continuation() {
        let stats = LamStats::new(vec![]);
        let ctx = CompileContext::effect_call(stats);

        let new_ctx = ctx.with_continuation(Continuation::Assign(Ident::create_local("x")));

        assert!(matches!(new_ctx.continuation, Continuation::Assign(_)));
    }

    #[test]
    fn test_return_label() {
        let id = Ident::create_local("return");
        let params = vec![Ident::create_local("a"), Ident::create_local("b")];
        let mask = vec![true, false];

        let mut label = ReturnLabel::new(id, params.clone(), mask.clone());

        assert_eq!(label.id, id);
        assert_eq!(label.params.len(), 2);
        assert!(!label.triggered);

        label.triggered = true;
        assert!(label.triggered);
    }

    #[test]
    fn test_tail_type() {
        let not_tail = TailType::NotTail;
        assert!(!not_tail.is_maybe_return());

        let maybe_tail = TailType::MaybeTailIsReturn(MaybeTail::TailInTry);
        assert!(maybe_tail.is_maybe_return());
    }
}
