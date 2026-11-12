//! Lambda IR - Intermediate representation for ReScript compilation.
//!
//! This module provides the Lambda IR, which sits between the typed AST
//! and the JavaScript IR in the compilation pipeline. The Lambda IR is
//! a simplified, imperative representation that makes code generation
//! and optimization easier.
//!
//! # Architecture
//!
//! The Lambda IR is organized into several submodules:
//!
//! - [`lam_constant`] - Lambda constants (literals, blocks, etc.)
//! - [`lam_primitive`] - Primitive operations (arithmetic, comparisons, etc.)
//! - [`lam_compat`] - Compatibility types (comparison, let_kind, etc.)
//! - [`lam_tag_info`] - Block tag information for variants and records
//! - [`lam_arity`] - Arity tracking for functions
//! - [`lam_analysis`] - Side effect and size analysis
//! - [`lam_closure`] - Closure and free variable analysis
//! - [`lam_subst`] - Variable substitution
//! - [`lam_beta_reduce`] - Beta reduction (function inlining)
//! - [`lam_print`] - Pretty printing for debugging
//! - [`lam_compile_context`] - Compilation context for Lambda to JS IR

pub mod arena;
pub mod js_exp_make;
pub mod js_pass_external_shadow;
pub mod js_pass_flatten_and_mark_dead;
pub mod js_pass_record_rest;
pub mod js_pass_tailcall_inline;
pub mod js_shake;
pub mod js_stmt_make;
pub mod lam_analysis;
pub mod lam_arity;
pub mod lam_beta_reduce;
pub mod lam_closure;
pub mod lam_coercion;
pub mod lam_compat;
pub mod lam_compile;
pub mod lam_compile_arguments;
pub mod lam_compile_const;
pub mod lam_compile_context;
pub mod lam_compile_external;
pub mod lam_compile_main;
pub mod lam_compile_primitive;
pub mod lam_compile_variant;
pub mod lam_constant;
pub mod lam_hit;
pub mod lam_loc;
pub mod lam_pass_alpha_conversion;
pub mod lam_pass_collapse_var_aliases;
pub mod lam_pass_collect;
pub mod lam_pass_deep_flatten;
pub mod lam_pass_exits;
pub mod lam_pass_guard_raises;
pub mod lam_pass_lets_dce;
pub mod lam_pass_remove_alias;
pub mod lam_pass_sroa;
pub mod lam_primitive;
pub mod lam_print;
pub mod lam_stats;
pub mod lam_subst;
pub mod lam_tag_info;
pub mod lam_util;
pub mod lambda_traverse;
pub mod printlambda;
pub mod sexp_lambda;
pub(crate) mod untagged_dispatch;

use crate::ident::Ident;
pub use lam_compat::{Comparison, FieldDbgInfo, LetKind, SetFieldDbgInfo};
pub use lam_constant::Constant;
pub use lam_loc::{CmjExportLambdas, LamLoc, LamLocTable};
pub use lam_primitive::Primitive;
pub use lam_tag_info::TagInfo;

/// `Translmod.flat_make_step`: a module field on the way to a nested `make`,
/// its runtime position (counted as in `Env`) and its source name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlatMakeStep {
    /// The field's runtime position.
    pub pos: i32,
    /// The field's source name.
    pub name: String,
}

/// `Translmod.flat_make_path`.
pub type FlatMakePath = Vec<FlatMakeStep>;

/// `Translmod.flat_export_name`: the segments, each unwrapped from `\"..."`,
/// joined with `$`.
pub fn flat_export_name<S: AsRef<str>>(path: &[S]) -> String {
    path.iter()
        .map(|part| {
            let part = part.as_ref();
            if part.len() >= 3 && part.starts_with("\\\"") && part.ends_with('"') {
                &part[2..part.len() - 1]
            } else {
                part
            }
        })
        .collect::<Vec<_>>()
        .join("$")
}

/// `Translmod.flat_make_name`: the flat export a read of this source path
/// from another module goes through, `Some("A$B$make")` for `A.B.make` and
/// `None` for other paths.
pub fn flat_make_name<S: AsRef<str>>(path: &[S]) -> Option<String> {
    match path {
        [_, _, ..] if path.last().is_some_and(|last| last.as_ref() == "make") => {
            Some(flat_export_name(path))
        }
        _ => None,
    }
}

/// Application status for function calls
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ApplyStatus {
    /// No special handling
    Na,
    /// Infer full application
    InferFull,
    /// Uncurried application
    Uncurry,
}

/// Inline attribute for functions
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize)]
pub enum InlineAttribute {
    /// Always inline this function
    Always,
    /// Never inline this function
    Never,
    /// Default inlining behavior
    #[default]
    Default,
}

/// Application info for function calls
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ApInfo {
    /// Source location handle (`ap_info.ap_loc`).
    pub loc: LamLoc,
    /// Application status
    pub status: ApplyStatus,
}

/// Function attributes
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct FunctionAttribute {
    /// Inline hint
    pub inline: InlineAttribute,
    /// Is this a functor?
    pub is_a_functor: bool,
    /// Does this function return unit?
    pub return_unit: bool,
    /// Is this an async function?
    pub async_: bool,
    /// Directive (e.g., "use server")
    pub directive: Option<String>,
    /// Does this function take a single unit argument?
    pub one_unit_arg: bool,
}

impl Default for FunctionAttribute {
    fn default() -> Self {
        Self {
            inline: InlineAttribute::Default,
            is_a_functor: false,
            return_unit: false,
            async_: false,
            directive: None,
            one_unit_arg: false,
        }
    }
}

/// Key selected by a Lambda switch branch.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum SwitchKey {
    /// An integer case: a constant constructor index or a block tag.
    Int(i32),
    /// A variant constructor case, dispatched by its runtime representation.
    Constructor(crate::types::VariantConstructorCase),
}

impl std::fmt::Display for SwitchKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int(value) => value.fmt(f),
            Self::Constructor(crate::types::VariantConstructorCase::Constant(tag)) => {
                write!(f, "constructor {:?}", tag.name)
            }
            Self::Constructor(crate::types::VariantConstructorCase::Block(block)) => {
                write!(f, "constructor {:?}", block.tag().name)
            }
        }
    }
}

/// lambda.ml `untagged_value`: the JavaScript value a constant is emitted as
/// by `Lam_compile_const` and `Js_dump`, not its source constructor. A
/// constant of another representation keeps the dispatch at run time.
pub(crate) fn untagged_value(c: &Constant) -> Option<untagged_dispatch::Value> {
    use crate::types::VariantLiteralTag as L;
    use untagged_dispatch::Value;
    Some(match c {
        Constant::String(s) | Constant::ImmString(s) => Value::Literal(L::String(s.clone())),
        Constant::Int { i, .. } => Value::Literal(L::Int(i64::from(*i))),
        Constant::NativeInt { i, .. } => Value::Literal(L::Int(i64::from(*i as i32))),
        Constant::Float(f) => Value::Literal(L::Float(f.clone())),
        Constant::JsTrue => Value::Literal(L::Bool(true)),
        Constant::JsFalse => Value::Literal(L::Bool(false)),
        Constant::JsNull => Value::Literal(L::Null),
        Constant::JsUndefined { .. } => Value::Literal(L::Undefined),
        // `Const_polyvar name`.
        Constant::Pointer(name) => Value::Literal(L::String(name.clone())),
        Constant::Constructor(tag) => Value::Literal(tag.literal.clone()),
        // `Bigint_utils.to_string sign digits`.
        Constant::BigInt { negative, value } => Value::Literal(L::BigInt(if *negative {
            format!("-{value}")
        } else {
            value.clone()
        })),
        Constant::Block { tag_info, .. } => match &**tag_info {
            TagInfo::Tuple => Value::Array,
            TagInfo::Record(record) if record.array => Value::Array,
            _ => Value::Object,
        },
        Constant::Char(_) | Constant::Some(_) | Constant::ModuleAlias => return None,
    })
}

/// lambda.ml `literal_denotes_same` = `Variant_runtime.same_literal_value`:
/// runtime equality, rather than equality of tags.
pub(crate) fn literal_denotes_same(
    a: &crate::types::VariantLiteralTag,
    b: &crate::types::VariantLiteralTag,
) -> bool {
    crate::types::variant_runtime::same_literal_value(a, b)
}

/// lambda.ml `untagged_plan`: the dispatch of a switch on an untagged
/// variant, which the code generator prints and constant folding evaluates.
/// A switch with literal arms and no payload arm left is a plain switch on
/// the literals. `arm` names an arm's action as the plan's body.
pub(crate) fn untagged_plan_with<'s, A: Clone>(
    sw_consts_full: bool,
    sw_consts: &'s [(SwitchKey, A)],
    sw_blocks_full: bool,
    sw_blocks: &'s [(SwitchKey, A)],
    sw_failaction: Option<A>,
    sw_dispatch: &'s SwitchDispatch,
    same: impl Fn(&A, &A) -> bool,
) -> Option<untagged_dispatch::Plan<A>> {
    let SwitchDispatch::Variant(facts) = sw_dispatch else {
        return None;
    };
    if shares_a_tag(sw_dispatch, sw_blocks.iter().map(|(key, _)| key)) {
        return shared_tag_plan(
            sw_consts_full,
            sw_consts,
            sw_blocks_full,
            sw_blocks,
            sw_failaction,
            facts,
            same,
        );
    }
    if facts.block_types.is_empty()
        || !((sw_consts_full && sw_consts.is_empty()) || !(sw_blocks_full && sw_blocks.is_empty()))
    {
        return None;
    }
    let literal_arms = sw_consts
        .iter()
        .map(|(key, action)| match key {
            SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(tag)) => {
                Some((tag.literal.clone(), action.clone()))
            }
            SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(_))
            | SwitchKey::Int(_) => None,
        })
        .collect::<Option<Vec<_>>>()?;
    // The declaration stored the order of its object cases; without it the
    // arms of several object cases would share one `typeof` test.
    let objects = facts
        .block_types
        .iter()
        .filter(|kind| **kind == crate::types::VariantBlockType::Object)
        .count();
    assert!(
        objects < 2 || facts.object_cases.len() == objects,
        "untagged variant with {objects} object cases and no stored order"
    );
    let mut payload_arms = Vec::with_capacity(sw_blocks.len());
    let mut object_arms = Vec::new();
    for (key, action) in sw_blocks {
        let SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
            crate::types::VariantBlock::Untagged { tag, block_type },
        )) = key
        else {
            return None;
        };
        // An object case of a variant with several is told apart by its
        // fields.
        match facts.object_cases.iter().position(|case| case.name == tag.name) {
            Some(position) if *block_type == crate::types::VariantBlockType::Object => {
                object_arms.push((position, action.clone()));
            }
            _ => payload_arms.push((block_type.clone(), action.clone())),
        }
    }
    Some(untagged_dispatch::plan(
        same,
        untagged_dispatch::Input {
            facts,
            literal_arms,
            payload_arms,
            object_arms,
            literals_complete: sw_consts_full,
            payloads_complete: sw_blocks_full,
            fallback: sw_failaction,
        },
    ))
}

/// Whether a switch on a tagged variant has an arm for a case whose tag
/// other cases share, so that the tag alone does not choose the arm.
pub(crate) fn shares_a_tag<'k>(
    dispatch: &SwitchDispatch,
    mut block_keys: impl Iterator<Item = &'k SwitchKey>,
) -> bool {
    let SwitchDispatch::Variant(facts) = dispatch else {
        return false;
    };
    !facts.shared_tags.is_empty()
        && block_keys.any(|key| match key {
            SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
                crate::types::VariantBlock::Tagged(block),
            )) => facts
                .shared_tag(&block.tag.literal)
                .is_some_and(|shared| shared.cases.iter().any(|case| case.name == block.tag.name)),
            _ => false,
        })
}

/// [`untagged_plan_with`] for a tagged variant whose cases share tags.
fn shared_tag_plan<A: Clone>(
    sw_consts_full: bool,
    sw_consts: &[(SwitchKey, A)],
    sw_blocks_full: bool,
    sw_blocks: &[(SwitchKey, A)],
    sw_failaction: Option<A>,
    facts: &crate::types::VariantMatchingFacts,
    same: impl Fn(&A, &A) -> bool,
) -> Option<untagged_dispatch::Plan<A>> {
    let literal_arms = sw_consts
        .iter()
        .map(|(key, action)| match key {
            SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(tag)) => {
                Some((tag.literal.clone(), action.clone()))
            }
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let block_arms = sw_blocks
        .iter()
        .map(|(key, action)| match key {
            SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
                crate::types::VariantBlock::Tagged(block),
            )) => Some((block.tag.literal.clone(), block.tag.name, action.clone())),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    Some(untagged_dispatch::shared_tag_plan(
        same,
        untagged_dispatch::SharedTagInput {
            facts,
            literal_arms,
            block_arms,
            literals_complete: sw_consts_full,
            blocks_complete: sw_blocks_full,
            fallback: sw_failaction,
        },
    ))
}

/// lambda.ml `untagged_plan` over the arms of a tree switch.
pub(crate) fn untagged_plan(switch: &LambdaSwitch) -> Option<untagged_dispatch::Plan<&Lambda>> {
    let consts: Vec<(SwitchKey, &Lambda)> =
        switch.sw_consts.iter().map(|(k, l)| (k.clone(), l)).collect();
    let blocks: Vec<(SwitchKey, &Lambda)> =
        switch.sw_blocks.iter().map(|(k, l)| (k.clone(), l)).collect();
    untagged_plan_with(
        switch.sw_consts_full,
        &consts,
        switch.sw_blocks_full,
        &blocks,
        switch.sw_failaction.as_deref(),
        &switch.sw_dispatch,
        |a: &&Lambda, b: &&Lambda| lambda_eq_approx(a, b),
    )
}

/// lambda.ml `switch`'s `same_runtime`: blocks compared by runtime value.
pub(crate) fn same_block_runtime(
    block: &crate::types::VariantBlock,
    case: &crate::types::VariantBlock,
) -> bool {
    match (block, case) {
        (crate::types::VariantBlock::Tagged(block), crate::types::VariantBlock::Tagged(case)) => {
            block.tag_name == case.tag_name
                && literal_denotes_same(&block.tag.literal, &case.tag.literal)
        }
        _ => block == case,
    }
}

/// Two blocks with a tag that several cases share are the same case only
/// when they are the same constructor: the tag does not tell them apart.
pub(crate) fn same_shared_case(
    dispatch: &SwitchDispatch,
    block: &crate::types::VariantBlock,
    case: &crate::types::VariantBlock,
) -> bool {
    match (dispatch, block, case) {
        (
            SwitchDispatch::Variant(facts),
            crate::types::VariantBlock::Tagged(block),
            crate::types::VariantBlock::Tagged(case),
        ) if facts.shared_tag(&case.tag.literal).is_some() => block.tag.name == case.tag.name,
        _ => true,
    }
}

/// Runtime dispatch semantics for a Lambda switch.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SwitchDispatch {
    /// Dispatch on integer indices and block tags.
    Direct,
    /// Dispatch on a variant's runtime representation, for untagged and
    /// custom-tagged variants.
    Variant(crate::types::VariantMatchingFacts),
}

/// Switch construct for pattern matching.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct LambdaSwitch {
    /// Whether the constant cases cover every constant constructor.
    pub sw_consts_full: bool,
    /// Constant cases and their actions.
    pub sw_consts: Vec<(SwitchKey, Lambda)>,
    /// Whether the block cases cover every block constructor.
    pub sw_blocks_full: bool,
    /// Block cases and their actions.
    pub sw_blocks: Vec<(SwitchKey, Lambda)>,
    /// The action taken when no case matches.
    pub sw_failaction: Option<Box<Lambda>>,
    /// How the runtime tells the cases apart.
    pub sw_dispatch: SwitchDispatch,
}

/// Runtime literal carried by an OCaml/ReScript variant tag.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SwitchCaseTag {
    /// A string literal tag.
    String(String),
    /// An integer literal tag.
    Int(i64),
    /// A float literal tag, in its source text.
    Float(String),
    /// A bigint literal tag, in its source text.
    BigInt(String),
    /// A boolean literal tag.
    Bool(bool),
    /// The `null` tag.
    Null,
    /// The `undefined` tag.
    Undefined,
}

/// Lambda function definition
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct LFunction {
    /// Number of arguments (arity)
    pub arity: i32,
    /// Parameter identifiers
    pub params: Vec<Ident>,
    /// Function body
    pub body: Box<Lambda>,
    /// Function attributes
    pub attr: FunctionAttribute,
    /// Source location (`lfunction.loc`, compiler/ml/lambda.mli:374-379),
    /// read by source maps (compiler/core/lam_compile.ml:436, 1829).
    pub loc: LamLoc,
}

/// Primitive operation info
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct PrimInfo {
    /// The primitive operation
    pub primitive: Primitive,
    /// Arguments to the primitive
    pub args: Vec<Lambda>,
    /// Source location handle
    pub loc: LamLoc,
}

/// Function application
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct Apply {
    /// Function being applied
    pub ap_func: Box<Lambda>,
    /// Arguments
    pub ap_args: Vec<Lambda>,
    /// Application info
    pub ap_info: ApInfo,
}

/// Lambda IR expression
///
/// This is the core representation used for code generation and optimization.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum Lambda {
    /// Variable reference
    Lvar(Ident),

    /// Global module reference (with dynamic import flag)
    LglobalModule(Ident),

    /// Constant value
    Lconst(Constant),

    /// Function application
    Lapply(Box<Apply>),

    /// Function definition
    Lfunction(Box<LFunction>),

    /// Let binding: let kind, identifier, value, body
    Llet(LetKind, Ident, Box<Lambda>, Box<Lambda>),

    /// Recursive let bindings
    Lletrec(Vec<(Ident, Lambda)>, Box<Lambda>),

    /// Primitive operation
    Lprim(Box<PrimInfo>),

    /// Switch on integer/block tag
    Lswitch(Box<Lambda>, Box<LambdaSwitch>),

    /// Switch on string value
    LstringSwitch(Box<Lambda>, Vec<(String, Lambda)>, Option<Box<Lambda>>),

    /// Raise a static exception
    LstaticRaise(i32, Vec<Lambda>),

    /// Catch a static exception: body, (exception id, params), handler
    LstaticCatch(Box<Lambda>, (i32, Vec<Ident>), Box<Lambda>),

    /// Try-with exception handling
    LtryWith(Box<Lambda>, Ident, Box<Lambda>),

    /// `Ltryfinally (body, finally)` (lambda.mli): evaluates `body`, then
    /// `finally` however `body` is left (normally, by an exception, or by
    /// break/continue/return), and has the value of `body`. A try with both
    /// catch and finally is an `LtryFinally` around an `LtryWith`.
    LtryFinally(Box<Lambda>, Box<Lambda>),

    /// If-then-else
    LifThenElse(Box<Lambda>, Box<Lambda>, Box<Lambda>),

    /// Sequence of expressions
    Lsequence(Box<Lambda>, Box<Lambda>),

    /// Break out of the enclosing loop (port of OCaml `Lbreak`)
    Lbreak,

    /// Continue to the next iteration of the enclosing loop (port of
    /// OCaml `Lcontinue`)
    Lcontinue,

    /// While loop
    Lwhile(Box<Lambda>, Box<Lambda>),

    /// For loop: variable, start, end, direction, body
    Lfor(Ident, Box<Lambda>, Box<Lambda>, DirectionFlag, Box<Lambda>),

    /// For-of loop: variable, iterable, body (upstream #7887).
    LforOf(Ident, Box<Lambda>, Box<Lambda>),

    /// For-await-of loop: variable, async iterable, body (upstream #7887).
    LforAwaitOf(Ident, Box<Lambda>, Box<Lambda>),

    /// Assignment to a mutable variable
    Lassign(Ident, Box<Lambda>),
}

/// Direction flag for for loops
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum DirectionFlag {
    /// Ascending (to)
    Upto,
    /// Descending (downto)
    Downto,
}

impl Lambda {
    /// Create a variable reference
    pub fn var(id: Ident) -> Self {
        Lambda::Lvar(id)
    }

    /// Create a global module reference
    pub fn global_module(id: Ident) -> Self {
        Lambda::LglobalModule(id)
    }

    /// Create a constant
    pub fn const_(c: Constant) -> Self {
        Lambda::Lconst(c)
    }

    /// Create a function
    pub fn function_(
        arity: i32,
        params: Vec<Ident>,
        body: Lambda,
        attr: FunctionAttribute,
        loc: LamLoc,
    ) -> Self {
        Lambda::Lfunction(Box::new(LFunction {
            arity,
            params,
            body: Box::new(body),
            attr,
            loc,
        }))
    }

    /// Create a let binding
    pub fn let_(kind: LetKind, id: Ident, value: Lambda, body: Lambda) -> Self {
        Lambda::Llet(kind, id, Box::new(value), Box::new(body))
    }

    /// Create recursive let bindings
    pub fn letrec(bindings: Vec<(Ident, Lambda)>, body: Lambda) -> Self {
        Lambda::Lletrec(bindings, Box::new(body))
    }

    /// Create a primitive operation. Direct port of OCaml's
    /// `Lam.prim` smart constructor (compiler/core/lam.ml:479-582):
    /// folds constants on unary/binary numeric and string ops, and
    /// collapses module aliasing makeblocks. Every fold below cites the
    /// exact OCaml line that justifies it.
    /// [`Lambda::prim`] for an already boxed payload: keeps the box unless one
    /// of `prim`'s constant folds can apply (one or two constant arguments,
    /// or a module-alias `Pmakeblock`).
    pub fn prim_boxed(info: Box<PrimInfo>) -> Self {
        let may_fold = matches!(
            info.args.as_slice(),
            [Lambda::Lconst(_)] | [Lambda::Lconst(_), Lambda::Lconst(_)]
        ) || matches!(info.primitive, Primitive::Pmakeblock(TagInfo::Module(_), _));
        if may_fold {
            let PrimInfo {
                primitive,
                args,
                loc,
            } = *info;
            Lambda::prim(primitive, args, loc)
        } else {
            Lambda::Lprim(info)
        }
    }

    /// `Lam.prim`: a primitive application, constant-folded where the operands
    /// allow (lam.ml:482-560).
    pub fn prim(primitive: Primitive, args: Vec<Lambda>, loc: LamLoc) -> Self {
        let default = |primitive: Primitive, args: Vec<Lambda>, loc: LamLoc| -> Lambda {
            Lambda::Lprim(Box::new(PrimInfo {
                primitive,
                args,
                loc,
            }))
        };

        match args.as_slice() {
            // lam.ml:482-498 — single-arg constant folds.
            [Lambda::Lconst(a)] => match (&primitive, a) {
                // lam.ml:484
                (Primitive::Pnegint, Constant::Int { i, .. }) => {
                    Lambda::Lconst(Constant::int(i.wrapping_neg()))
                }
                // lam.ml:487-488 — Pintoffloat (float as string -> int via parse).
                (Primitive::Pintoffloat, Constant::Float(s)) => match s.parse::<f64>() {
                    Ok(f) => Lambda::Lconst(Constant::int(f as i32)),
                    Err(_) => default(primitive, args, loc),
                },
                // lam.ml:491-492 — Pstringlength on bare string literal.
                (Primitive::Pstringlength, Constant::String(s)) => Lambda::Lconst(Constant::int(
                    crate::string_literal::utf16_length(s)
                        .expect("String_literal.utf16_length: Invalid_utf8")
                        as i32,
                )),
                // lam.ml:496-497
                (Primitive::Pnot, Constant::JsTrue) => Lambda::false_(),
                (Primitive::Pnot, Constant::JsFalse) => Lambda::true_(),
                _ => default(primitive, args, loc),
            },
            // lam.ml:499-548 — two-arg constant folds.
            [Lambda::Lconst(a), Lambda::Lconst(b)] => match (&primitive, a, b) {
                // lam.ml:501-502
                (
                    Primitive::Pintcomp(cmp),
                    Constant::Int { i: ai, .. },
                    Constant::Int { i: bi, .. },
                ) => Lambda::Lconst(if cmp.cmp_int32(*ai, *bi) {
                    Constant::JsTrue
                } else {
                    Constant::JsFalse
                }),
                // lam.ml:503-506 — Pfloatcomp (parsed from string).
                (Primitive::Pfloatcomp(cmp), Constant::Float(af), Constant::Float(bf)) => {
                    match (af.parse::<f64>(), bf.parse::<f64>()) {
                        (Ok(av), Ok(bv)) => Lambda::Lconst(if cmp.cmp_float(av, bv) {
                            Constant::JsTrue
                        } else {
                            Constant::JsFalse
                        }),
                        _ => default(primitive, args, loc),
                    }
                }
                // lam.ml:508-513 — Pintcomp Eq/Neq on two pointers (poly-variant tags).
                (
                    Primitive::Pintcomp(op @ (Comparison::Eq | Comparison::Neq)),
                    Constant::Pointer(ai),
                    Constant::Pointer(bi),
                ) => {
                    let eq = ai == bi;
                    let result = match op {
                        Comparison::Eq => eq,
                        Comparison::Neq => !eq,
                        _ => unreachable!(),
                    };
                    Lambda::Lconst(if result {
                        Constant::JsTrue
                    } else {
                        Constant::JsFalse
                    })
                }
                // lam.ml:514-532 — int arithmetic (skip Pdivint/Pmodint when bb=0).
                (
                    Primitive::Paddint
                    | Primitive::Psubint
                    | Primitive::Pmulint
                    | Primitive::Pdivint
                    | Primitive::Pmodint
                    | Primitive::Pandint
                    | Primitive::Porint
                    | Primitive::Pxorint
                    | Primitive::Plslint
                    | Primitive::Plsrint
                    | Primitive::Pasrint,
                    Constant::Int { i: aa, .. },
                    Constant::Int { i: bb, .. },
                ) => match &primitive {
                    Primitive::Paddint => Lambda::Lconst(Constant::int(aa.wrapping_add(*bb))),
                    Primitive::Psubint => Lambda::Lconst(Constant::int(aa.wrapping_sub(*bb))),
                    Primitive::Pmulint => Lambda::Lconst(Constant::int(aa.wrapping_mul(*bb))),
                    Primitive::Pdivint => {
                        if *bb == 0 {
                            default(primitive, args, loc)
                        } else {
                            Lambda::Lconst(Constant::int(aa.wrapping_div(*bb)))
                        }
                    }
                    Primitive::Pmodint => {
                        if *bb == 0 {
                            default(primitive, args, loc)
                        } else {
                            Lambda::Lconst(Constant::int(aa.wrapping_rem(*bb)))
                        }
                    }
                    Primitive::Pandint => Lambda::Lconst(Constant::int(aa & bb)),
                    Primitive::Porint => Lambda::Lconst(Constant::int(aa | bb)),
                    Primitive::Pxorint => Lambda::Lconst(Constant::int(aa ^ bb)),
                    Primitive::Plslint => {
                        Lambda::Lconst(Constant::int(aa.wrapping_shl(*bb as u32)))
                    }
                    Primitive::Plsrint => {
                        let result = (*aa as u32).wrapping_shr(*bb as u32) as i32;
                        Lambda::Lconst(Constant::int(result))
                    }
                    Primitive::Pasrint => {
                        Lambda::Lconst(Constant::int(aa.wrapping_shr(*bb as u32)))
                    }
                    _ => unreachable!(),
                },
                // lam.ml:533-538 — Psequand / Psequor on JsTrue/JsFalse pairs.
                (Primitive::Psequand, Constant::JsFalse, Constant::JsTrue | Constant::JsFalse) => {
                    Lambda::false_()
                }
                (Primitive::Psequand, Constant::JsTrue, Constant::JsTrue) => Lambda::true_(),
                (Primitive::Psequand, Constant::JsTrue, Constant::JsFalse) => Lambda::false_(),
                (Primitive::Psequor, Constant::JsTrue, Constant::JsTrue | Constant::JsFalse) => {
                    Lambda::true_()
                }
                (Primitive::Psequor, Constant::JsFalse, Constant::JsTrue) => Lambda::true_(),
                (Primitive::Psequor, Constant::JsFalse, Constant::JsFalse) => Lambda::false_(),
                // lam.ml:539-542
                (Primitive::Pstringadd, Constant::String(a_s), Constant::String(b_s)) => {
                    Lambda::Lconst(Constant::String(format!("{}{}", a_s, b_s)))
                }
                // lam.ml:543-547 — Pstringrefs / Pstringrefu on (String, Int).
                (
                    Primitive::Pstringrefs | Primitive::Pstringrefu,
                    Constant::String(s),
                    Constant::Int { i: idx, .. },
                ) => match crate::string_literal::code_point_at_utf16_index(s, *idx as i64) {
                    Ok(Some(codepoint)) => Lambda::Lconst(Constant::Char(codepoint as i32)),
                    _ => default(primitive, args, loc),
                },
                _ => default(primitive, args, loc),
            },
            // lam.ml:549-582 — `Pmakeblock( Blk_module fields, _)` arm of
            // `Lam.prim`. When every argument `args.[i]` is
            // `Pfield(i, Fld_module {name = fields.[i]}) [Lglobal_module v | Lvar v]`
            // referencing the SAME source module `v`, the makeblock collapses
            // to that module reference — the code reconstruction is exactly
            // the source alias. This turns `{ x0: y.x0, x1: y.x1 }` back into
            // `y`, matching OCaml's module-alias output (`return U` vs the
            // expanded object literal).
            _ => fold_makeblock_module_alias(&primitive, &args)
                .unwrap_or_else(|| default(primitive, args, loc)),
        }
    }

    /// Create a switch using OCaml's `Lam.switch` smart constructor.
    pub fn switch(scrutinee: Lambda, switch: LambdaSwitch) -> Self {
        let keep = |scrutinee: Lambda, switch: LambdaSwitch| {
            Lambda::Lswitch(Box::new(scrutinee), Box::new(switch))
        };
        // lambda.ml `action_or_switch`.
        fn action_or_switch(
            action: Option<Lambda>,
            scrutinee: Lambda,
            switch: LambdaSwitch,
        ) -> Lambda {
            match action {
                Some(action) => action,
                None => match &switch.sw_failaction {
                    Some(action) => (**action).clone(),
                    None => Lambda::Lswitch(Box::new(scrutinee), Box::new(switch)),
                },
            }
        }
        // An untagged variant is dispatched on the value, so a constant
        // scrutinee takes the arm the generated code takes for its JavaScript
        // value, not the arm of the constructor it was written with.
        if let Lambda::Lconst(cst) = &scrutinee
            && let SwitchDispatch::Variant(facts) = &switch.sw_dispatch
            && !facts.block_types.is_empty()
        {
            let outcome = match (untagged_plan(&switch), untagged_value(cst)) {
                (Some(plan), Some(value)) => Some(
                    match untagged_dispatch::select(&plan, &value, &mut |_| ()) {
                        untagged_dispatch::Outcome::Arm(action) => Some(Some(action.clone())),
                        untagged_dispatch::Outcome::Default => Some(None),
                        untagged_dispatch::Outcome::Nothing => None,
                    },
                ),
                _ => None,
            };
            return match outcome.flatten() {
                Some(Some(action)) => action,
                Some(None) => action_or_switch(None, scrutinee, switch),
                None => keep(scrutinee, switch),
            };
        }
        match scrutinee {
            Lambda::Lconst(Constant::Constructor(tag)) => {
                // By runtime value: a coercion accepts `@as(1.)` for `@as(1.0)`.
                let action = switch.sw_consts.iter().find(|(key, _)| matches!(
                    key,
                    SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(candidate))
                        if literal_denotes_same(&tag.literal, &candidate.literal)
                )).map(|(_, branch)| branch.clone());
                action_or_switch(action, Lambda::Lconst(Constant::Constructor(tag)), switch)
            }
            Lambda::Lconst(constant @ Constant::Int { i, .. }) => {
                let literal = crate::types::VariantLiteralTag::Int(i64::from(i));
                let action = switch
                    .sw_consts
                    .iter()
                    .find(|(key, _)| match key {
                        SwitchKey::Int(value) => *value == i,
                        // A constant represented as a number, compared by value.
                        SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(
                            tag,
                        )) => literal_denotes_same(&literal, &tag.literal),
                        SwitchKey::Constructor(_) => false,
                    })
                    .map(|(_, branch)| branch.clone());
                action_or_switch(action, Lambda::Lconst(constant), switch)
            }
            Lambda::Lconst(Constant::Block { tag_info, elements }) => {
                let runtime = match &*tag_info {
                    TagInfo::Constructor(c) => {
                        Some(crate::types::VariantBlock::Tagged((*c.runtime).clone()))
                    }
                    TagInfo::RecordInlined(r) => Some((*r.runtime).clone()),
                    _ => None,
                };
                let action = switch
                    .sw_blocks
                    .iter()
                    .find(|(key, _)| matches!(
                        (key, runtime.as_ref()),
                        (
                            SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(candidate)),
                            Some(runtime)
                        ) if same_block_runtime(runtime, candidate)
                            && same_shared_case(&switch.sw_dispatch, runtime, candidate)
                    ))
                    .map(|(_, branch)| branch.clone());
                action_or_switch(
                    action,
                    Lambda::Lconst(Constant::Block { tag_info, elements }),
                    switch,
                )
            }
            other => keep(other, switch),
        }
    }

    /// Create a string switch using OCaml's `Lam.stringswitch` smart constructor.
    pub fn string_switch(
        scrutinee: Lambda,
        cases: Vec<(String, Lambda)>,
        default: Option<Box<Lambda>>,
    ) -> Self {
        let matched = |value: &str| {
            cases
                .iter()
                .find(|(tag, _)| tag == value)
                .map(|(_, branch)| branch.clone())
                .or_else(|| default.as_deref().cloned())
        };

        match scrutinee {
            Lambda::Lconst(ref constant @ Constant::String(ref s)) => {
                matched(s).unwrap_or_else(|| {
                    Lambda::LstringSwitch(
                        Box::new(Lambda::Lconst(constant.clone())),
                        cases,
                        default,
                    )
                })
            }
            Lambda::Lconst(ref constant @ Constant::ImmString(ref s)) => {
                matched(s).unwrap_or_else(|| {
                    Lambda::LstringSwitch(
                        Box::new(Lambda::Lconst(constant.clone())),
                        cases,
                        default,
                    )
                })
            }
            other => Lambda::LstringSwitch(Box::new(other), cases, default),
        }
    }

    /// Create a function application using OCaml's `Lam.apply` smart constructor.
    pub fn apply(func: Lambda, args: Vec<Lambda>, ap_info: ApInfo) -> Self {
        match func {
            Lambda::Lfunction(function) => {
                if let Some(reduced) = eta_reduce_function_apply(&function, &args, &ap_info) {
                    return reduced;
                }
                make_lapply(Lambda::Lfunction(function), args, ap_info)
            }
            Lambda::Llet(kind, id, value, body) => match *body {
                body @ Lambda::Lfunction(_) => {
                    Lambda::let_(kind, id, *value, Lambda::apply(body, args, ap_info))
                }
                body => make_lapply(Lambda::Llet(kind, id, value, Box::new(body)), args, ap_info),
            },
            func => make_lapply(func, args, ap_info),
        }
    }

    /// Create a sequence
    pub fn seq(first: Lambda, second: Lambda) -> Self {
        match first {
            Lambda::Lprim(__prim8)
                if matches!(__prim8.as_ref(), PrimInfo {
                    primitive: _primitive @ Primitive::Pmakeblock(_, _),
                    args: _,
                    loc: _,
                }) =>
            {
                let PrimInfo {
                    primitive: primitive @ Primitive::Pmakeblock(_, _),
                    args,
                    loc,
                } = *__prim8
                else {
                    unreachable!()
                };

                let mut args = args.into_iter();
                let Some(first_arg) = args.next() else {
                    return Lambda::Lsequence(
                        Box::new(Lambda::Lprim(Box::new(PrimInfo {
                            primitive,
                            args: Vec::new(),
                            loc,
                        }))),
                        Box::new(second),
                    );
                };
                Lambda::seq(args.fold(first_arg, Lambda::seq), second)
            }
            Lambda::Lprim(__prim7)
                if matches!(__prim7.as_ref(), PrimInfo {
                primitive: Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt,
                args,
                ..
            } if args.len() == 1) =>
            {
                let PrimInfo {
                    primitive: Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt,
                    mut args,
                    ..
                } = *__prim7
                else {
                    unreachable!()
                };
                Lambda::seq(args.remove(0), second)
            }
            first => Lambda::Lsequence(Box::new(first), Box::new(second)),
        }
    }

    /// Create an if-then-else
    pub fn if_(cond: Lambda, then_: Lambda, else_: Lambda) -> Self {
        match cond {
            Lambda::Lconst(constant) => {
                if constant.eval_as_bool() {
                    then_
                } else {
                    else_
                }
            }
            cond => {
                if is_assertfalse(&else_) {
                    return Lambda::seq(cond, then_);
                }
                if is_assertfalse(&then_) {
                    return Lambda::seq(cond, else_);
                }

                if matches!(
                    (&then_, &else_),
                    (
                        Lambda::Lconst(Constant::JsTrue),
                        Lambda::Lconst(Constant::JsFalse)
                    )
                ) {
                    return if has_boolean_type(&cond).is_some() {
                        cond
                    } else {
                        make_if(cond, then_, else_)
                    };
                }

                if matches!(
                    (&then_, &else_),
                    (
                        Lambda::Lconst(Constant::JsFalse),
                        Lambda::Lconst(Constant::JsTrue)
                    )
                ) {
                    return match has_boolean_type(&cond) {
                        Some(loc) => lambda_not(loc, cond),
                        None => make_if(cond, then_, else_),
                    };
                }

                // `if a then raise e else c` -> `(if a then raise e else ()); c`
                // is code motion, not normalization; it is the final
                // `lam_pass_guard_raises` pass (compiler/ml/lambda.ml if_).

                make_if(cond, then_, else_)
            }
        }
    }

    /// Create a while loop
    pub fn while_(cond: Lambda, body: Lambda) -> Self {
        Lambda::Lwhile(Box::new(cond), Box::new(body))
    }

    /// Break out of the enclosing loop. Port of OCaml `Lam.break`.
    pub fn break_() -> Self {
        Lambda::Lbreak
    }

    /// Continue the enclosing loop. Port of OCaml `Lam.continue`.
    pub fn continue_() -> Self {
        Lambda::Lcontinue
    }

    /// Create a for loop
    pub fn for_(var: Ident, start: Lambda, end: Lambda, dir: DirectionFlag, body: Lambda) -> Self {
        Lambda::Lfor(var, Box::new(start), Box::new(end), dir, Box::new(body))
    }

    /// Create a for-of loop. Port of OCaml `Lam.for_of`.
    pub fn for_of(var: Ident, iterable: Lambda, body: Lambda) -> Self {
        Lambda::LforOf(var, Box::new(iterable), Box::new(body))
    }

    /// Create a for-await-of loop. Port of OCaml `Lam.for_await_of`.
    pub fn for_await_of(var: Ident, iterable: Lambda, body: Lambda) -> Self {
        Lambda::LforAwaitOf(var, Box::new(iterable), Box::new(body))
    }

    /// Create a try-with block
    pub fn try_(body: Lambda, exn: Ident, handler: Lambda) -> Self {
        Lambda::LtryWith(Box::new(body), exn, Box::new(handler))
    }

    /// lambda.ml `try_finally`.
    pub fn try_finally(body: Lambda, finally: Lambda) -> Self {
        Lambda::LtryFinally(Box::new(body), Box::new(finally))
    }

    /// Create an assignment
    pub fn assign(var: Ident, value: Lambda) -> Self {
        Lambda::Lassign(var, Box::new(value))
    }

    /// Create a static raise
    pub fn static_raise(id: i32, args: Vec<Lambda>) -> Self {
        Lambda::LstaticRaise(id, args)
    }

    /// Create a static catch
    pub fn static_catch(
        body: Lambda,
        handler_id: i32,
        params: Vec<Ident>,
        handler: Lambda,
    ) -> Self {
        Lambda::LstaticCatch(Box::new(body), (handler_id, params), Box::new(handler))
    }

    /// JS true constant
    pub fn true_() -> Self {
        Lambda::Lconst(Constant::JsTrue)
    }

    /// JS false constant
    pub fn false_() -> Self {
        Lambda::Lconst(Constant::JsFalse)
    }

    /// Unit constant
    pub fn unit() -> Self {
        Lambda::Lconst(Constant::JsUndefined { is_unit: true })
    }

    /// Check if this is the unit value (undefined with is_unit=true)
    pub fn is_unit(&self) -> bool {
        matches!(
            self,
            Lambda::Lconst(Constant::JsUndefined { is_unit: true })
        )
    }
}

fn eta_reduce_function_apply(
    function: &LFunction,
    args: &[Lambda],
    ap_info: &ApInfo,
) -> Option<Lambda> {
    match function.body.as_ref() {
        Lambda::Lprim(__prim4)
            if matches!(
                __prim4.as_ref(),
                PrimInfo {
                    primitive: Primitive::PnullToOpt
                        | Primitive::PnullUndefinedToOpt
                        | Primitive::PisNull
                        | Primitive::PisNullUndefined
                        | Primitive::Ptypeof,
                    args: _wrap_args,
                    ..
                }
            ) =>
        {
            let PrimInfo {
                primitive:
                    Primitive::PnullToOpt
                    | Primitive::PnullUndefinedToOpt
                    | Primitive::PisNull
                    | Primitive::PisNullUndefined
                    | Primitive::Ptypeof,
                args: wrap_args,
                ..
            } = __prim4.as_ref()
            else {
                unreachable!()
            };

            let [Lambda::Lprim(inner_call)] = wrap_args.as_slice() else {
                return None;
            };
            let eta_args = eta_conversion_args(&function.params, &inner_call.args, args)?;
            // lambda.ml `apply` builds the result through the folding `prim`.
            let wrap = function_primitive(function.body.as_ref())?;
            let inner = Lambda::prim(inner_call.primitive.clone(), eta_args, ap_info.loc);
            Some(Lambda::prim(wrap, vec![inner], ap_info.loc))
        }
        Lambda::Lprim(inner_call) => {
            let eta_args = eta_conversion_args(&function.params, &inner_call.args, args)?;
            Some(Lambda::prim(
                inner_call.primitive.clone(),
                eta_args,
                ap_info.loc,
            ))
        }
        Lambda::Lsequence(first, second) => {
            let Lambda::Lprim(inner_call) = first.as_ref() else {
                return None;
            };
            let Lambda::Lconst(constant) = second.as_ref() else {
                return None;
            };
            let eta_args = eta_conversion_args(&function.params, &inner_call.args, args)?;
            Some(Lambda::seq(
                Lambda::prim(inner_call.primitive.clone(), eta_args, ap_info.loc),
                Lambda::Lconst(constant.clone()),
            ))
        }
        _ => None,
    }
}

fn function_primitive(body: &Lambda) -> Option<Primitive> {
    match body {
        Lambda::Lprim(__prim3) => {
            let PrimInfo { primitive, .. } = __prim3.as_ref();
            Some(primitive.clone())
        }
        _ => None,
    }
}

fn eta_conversion_args(
    params: &[Ident],
    inner_args: &[Lambda],
    outer_args: &[Lambda],
) -> Option<Vec<Lambda>> {
    if params.len() != inner_args.len() || params.len() != outer_args.len() {
        return None;
    }

    params
        .iter()
        .zip(inner_args.iter())
        .zip(outer_args.iter())
        .map(|((param, inner_arg), outer_arg)| match inner_arg {
            Lambda::Lvar(id) if param.same(id) => Some(outer_arg.clone()),
            _ => None,
        })
        .collect()
}

fn make_lapply(func: Lambda, args: Vec<Lambda>, ap_info: ApInfo) -> Lambda {
    Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(func),
        ap_args: args,
        ap_info,
    }))
}

fn make_if(cond: Lambda, then_: Lambda, else_: Lambda) -> Lambda {
    Lambda::LifThenElse(Box::new(cond), Box::new(then_), Box::new(else_))
}

fn is_assertfalse(lam: &Lambda) -> bool {
    matches!(
        lam,
        Lambda::Lconst(Constant::Int { comment: Some(info), .. })
            if matches!(**info, lam_constant::PointerInfo::AssertFalse)
    )
}

/// Direct port of OCaml's `Lam.prim` Blk_module collapse arm (lam.ml:551-575).
///
/// Recognises `Pmakeblock( Blk_module fields, _) [arg0; arg1; …]` where
/// every `argi` has the shape `Pfield(i, Fld_module {name = fields.[i]}) [src]`
/// and every `src` is the SAME `Lglobal_module v` or `Lvar v`. Returns that
/// module reference — the makeblock is reconstructing the source module
/// exactly, so the alias can be expressed as a single variable.
fn fold_makeblock_module_alias(primitive: &Primitive, args: &[Lambda]) -> Option<Lambda> {
    let Primitive::Pmakeblock(TagInfo::Module(fields), _) = primitive else {
        return None;
    };

    if fields.len() != args.len() || fields.is_empty() {
        return None;
    }

    // Inspect the first argument to discover both the source module (`Lglobal_module`
    // or `Lvar`) and to verify field 0 of the makeblock indeed maps to position 0
    // of that module with a matching name — mirrors the `pos = 0 && field1 = f1`
    // test in OCaml at lam.ml:566-573.
    let first = args.first()?;
    let Lambda::Lprim(__prim201) = first else {
        return None;
    };
    let PrimInfo {
        primitive: Primitive::Pfield(pos, lam_compat::FieldDbgInfo::Module { name: f1 }),
        args: first_args,
        ..
    } = __prim201.as_ref()
    else {
        return None;
    };
    if *pos != 0 || f1 != &fields[0] {
        return None;
    }
    if first_args.len() != 1 {
        return None;
    }
    let source_ident = match &first_args[0] {
        Lambda::LglobalModule(v) => *v,
        Lambda::Lvar(v) => *v,
        _ => return None,
    };
    let source_lam = first_args[0].clone();

    // Now verify every subsequent arg has the same shape and references the
    // SAME source module — mirrors the recursive `aux` helper at
    // lam.ml:552-563.
    for (i, (arg, expected_name)) in args.iter().zip(fields.iter()).enumerate().skip(1) {
        let Lambda::Lprim(__prim200) = arg else {
            return None;
        };
        let PrimInfo {
            primitive: Primitive::Pfield(pos, lam_compat::FieldDbgInfo::Module { name }),
            args: inner_args,
            ..
        } = __prim200.as_ref()
        else {
            return None;
        };
        if *pos as usize != i || name != expected_name {
            return None;
        }
        if inner_args.len() != 1 {
            return None;
        }
        let inner_same = match &inner_args[0] {
            Lambda::LglobalModule(v) | Lambda::Lvar(v) => v.same(&source_ident),
            _ => false,
        };
        if !inner_same {
            return None;
        }
    }

    Some(source_lam)
}

fn lambda_not(loc: LamLoc, lam: Lambda) -> Lambda {
    match lam {
        Lambda::Lprim(__prim2)
            if matches!(
                __prim2.as_ref(),
                PrimInfo {
                    primitive: Primitive::Pintcomp(Comparison::Neq),
                    args: _,
                    loc: _,
                }
            ) =>
        {
            let PrimInfo {
                primitive: Primitive::Pintcomp(Comparison::Neq),
                args,
                loc,
            } = *__prim2
            else {
                unreachable!()
            };
            Lambda::Lprim(Box::new(PrimInfo {
                primitive: Primitive::Pintcomp(Comparison::Eq),
                args,
                loc,
            }))
        }
        lam => Lambda::prim(Primitive::Pnot, vec![lam], loc),
    }
}

fn has_boolean_type(lam: &Lambda) -> Option<LamLoc> {
    match lam {
        Lambda::Lprim(__prim1)
            if matches!(
                __prim1.as_ref(),
                PrimInfo {
                    primitive: Primitive::Pnot
                        | Primitive::Psequand
                        | Primitive::Psequor
                        | Primitive::PisNotNone
                        | Primitive::Pobjcomp(_)
                        | Primitive::Pboolcomp(_)
                        | Primitive::Pintcomp(_)
                        | Primitive::Pfloatcomp(_)
                        | Primitive::Pbigintcomp(_)
                        | Primitive::Pstringcomp(_),
                    ..
                }
            ) =>
        {
            let PrimInfo {
                primitive:
                    Primitive::Pnot
                    | Primitive::Psequand
                    | Primitive::Psequor
                    | Primitive::PisNotNone
                    | Primitive::Pobjcomp(_)
                    | Primitive::Pboolcomp(_)
                    | Primitive::Pintcomp(_)
                    | Primitive::Pfloatcomp(_)
                    | Primitive::Pbigintcomp(_)
                    | Primitive::Pstringcomp(_),
                loc,
                ..
            } = __prim1.as_ref()
            else {
                unreachable!()
            };
            Some(*loc)
        }
        _ => None,
    }
}

fn lambda_eq_approx(lhs: &Lambda, rhs: &Lambda) -> bool {
    match (lhs, rhs) {
        (Lambda::LglobalModule(i1), Lambda::LglobalModule(i2)) => i1.same(i2),
        (Lambda::Lvar(i1), Lambda::Lvar(i2)) => i1.same(i2),
        (Lambda::Lconst(c1), Lambda::Lconst(c2)) => c1.eq_approx(c2),
        (Lambda::Lapply(app1), Lambda::Lapply(app2)) => {
            lambda_eq_approx(&app1.ap_func, &app2.ap_func)
                && lambda_list_eq_approx(&app1.ap_args, &app2.ap_args)
        }
        (Lambda::LifThenElse(a1, b1, c1), Lambda::LifThenElse(a2, b2, c2)) => {
            lambda_eq_approx(a1, a2) && lambda_eq_approx(b1, b2) && lambda_eq_approx(c1, c2)
        }
        (Lambda::Lsequence(a1, b1), Lambda::Lsequence(a2, b2))
        | (Lambda::Lwhile(a1, b1), Lambda::Lwhile(a2, b2)) => {
            lambda_eq_approx(a1, a2) && lambda_eq_approx(b1, b2)
        }
        (Lambda::Lbreak, Lambda::Lbreak) | (Lambda::Lcontinue, Lambda::Lcontinue) => true,
        // OCaml `Lam.eq_approx`: Lfor / LforOf / LforAwaitOf are
        // conservatively false (mirrors `compiler/core/lam.ml` `eq_approx`).
        // Falls through to the catch-all `_ => false` below.
        (Lambda::Lassign(v1, l1), Lambda::Lassign(v2, l2)) => {
            v1.same(v2) && lambda_eq_approx(l1, l2)
        }
        (Lambda::LstaticRaise(id1, args1), Lambda::LstaticRaise(id2, args2)) => {
            id1 == id2 && lambda_list_eq_approx(args1, args2)
        }
        (Lambda::Lprim(info1), Lambda::Lprim(info2)) => {
            info1.primitive.eq_approx(&info2.primitive)
                && lambda_list_eq_approx(&info1.args, &info2.args)
        }
        (
            Lambda::LstringSwitch(arg1, cases1, default1),
            Lambda::LstringSwitch(arg2, cases2, default2),
        ) => {
            lambda_eq_approx(arg1, arg2)
                && lambda_option_eq_approx(default1, default2)
                && cases1.len() == cases2.len()
                && cases1
                    .iter()
                    .zip(cases2.iter())
                    .all(|((name1, lam1), (name2, lam2))| {
                        name1 == name2 && lambda_eq_approx(lam1, lam2)
                    })
        }
        _ => false,
    }
}

fn lambda_list_eq_approx(lhs: &[Lambda], rhs: &[Lambda]) -> bool {
    lhs.len() == rhs.len()
        && lhs
            .iter()
            .zip(rhs.iter())
            .all(|(lhs, rhs)| lambda_eq_approx(lhs, rhs))
}

fn lambda_option_eq_approx(lhs: &Option<Box<Lambda>>, rhs: &Option<Box<Lambda>>) -> bool {
    match (lhs, rhs) {
        (None, None) => true,
        (Some(lhs), Some(rhs)) => lambda_eq_approx(lhs, rhs),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lambda_creation() {
        let id = Ident::create_local("x");
        let var = Lambda::var(id);

        match var {
            Lambda::Lvar(ref i) => assert_eq!(i.name(), "x"),
            _ => panic!("Expected Lvar"),
        }
    }

    #[test]
    fn test_let_binding() {
        let x = Ident::create_local("x");
        let _y = Ident::create_local("y");

        let binding = Lambda::let_(
            LetKind::Strict,
            x,
            Lambda::const_(Constant::Int {
                i: 42,
                comment: None,
            }),
            Lambda::var(x),
        );

        match binding {
            Lambda::Llet(LetKind::Strict, ref id, _, _) => {
                assert_eq!(id.name(), "x");
            }
            _ => panic!("Expected Llet"),
        }
    }

    #[test]
    fn test_function() {
        let x = Ident::create_local("x");
        let func = Lambda::function_(
            1,
            vec![x],
            Lambda::var(x),
            FunctionAttribute::default(),
            LamLoc::NONE,
        );

        match func {
            Lambda::Lfunction(ref f) => {
                assert_eq!(f.arity, 1);
                assert_eq!(f.params.len(), 1);
            }
            _ => panic!("Expected Lfunction"),
        }
    }

    #[test]
    fn test_if_then_else() {
        let cond = Lambda::var(Ident::create_local("cond"));
        let then_ = Lambda::const_(Constant::Int {
            i: 1,
            comment: None,
        });
        let else_ = Lambda::const_(Constant::Int {
            i: 0,
            comment: None,
        });

        let if_expr = Lambda::if_(cond, then_, else_);

        match if_expr {
            Lambda::LifThenElse(_, _, _) => {}
            _ => panic!("Expected LifThenElse"),
        }
    }

    #[test]
    fn test_if_then_else_constant_fold() {
        let then_ = Lambda::const_(Constant::Int {
            i: 1,
            comment: None,
        });
        let else_ = Lambda::const_(Constant::Int {
            i: 0,
            comment: None,
        });

        let if_expr = Lambda::if_(Lambda::true_(), then_.clone(), else_);
        match if_expr {
            Lambda::Lconst(Constant::Int {
                i: 1,
                comment: None,
            }) => {}
            _ => panic!("Expected folded then-branch"),
        }

        let if_expr = Lambda::if_(Lambda::false_(), then_, Lambda::unit());
        assert!(matches!(
            if_expr,
            Lambda::Lconst(Constant::JsUndefined { is_unit: true })
        ));
    }

    #[test]
    fn test_if_then_else_assertfalse_sequences_then_branch() {
        let cond_id = Ident::create_local("cond");
        let cond = Lambda::var(cond_id);
        let then_ = Lambda::const_(Constant::int(1));
        let assertfalse = Lambda::const_(Constant::Int {
            i: 0,
            comment: Some(Box::new(lam_constant::PointerInfo::AssertFalse)),
        });

        let if_expr = Lambda::if_(cond.clone(), then_.clone(), assertfalse);

        match if_expr {
            Lambda::Lsequence(first, second) => {
                assert!(matches!(*first, Lambda::Lvar(ref id) if id.same(&cond_id)));
                assert!(lambda_eq_approx(&second, &then_));
            }
            _ => panic!("Expected assertfalse branch to lower to sequence"),
        }
    }

    #[test]
    fn test_if_then_else_true_false_returns_boolean_condition() {
        let x = Ident::create_local("x");
        let cond = Lambda::prim(
            Primitive::Pintcomp(Comparison::Eq),
            vec![Lambda::var(x), Lambda::const_(Constant::int(0))],
            LamLoc::NONE,
        );

        let if_expr = Lambda::if_(cond.clone(), Lambda::true_(), Lambda::false_());
        assert!(lambda_eq_approx(&if_expr, &cond));
    }

    #[test]
    fn test_if_then_else_false_true_negates_boolean_condition() {
        let x = Ident::create_local("x");
        let if_expr = Lambda::if_(
            Lambda::prim(
                Primitive::Pintcomp(Comparison::Neq),
                vec![Lambda::var(x), Lambda::const_(Constant::int(0))],
                LamLoc::NONE,
            ),
            Lambda::false_(),
            Lambda::true_(),
        );

        match if_expr {
            Lambda::Lprim(__prim0)
                if matches!(
                    __prim0.as_ref(),
                    PrimInfo {
                        primitive: Primitive::Pintcomp(Comparison::Eq),
                        ..
                    }
                ) =>
            {
                let PrimInfo {
                    primitive: Primitive::Pintcomp(Comparison::Eq),
                    ..
                } = *__prim0
                else {
                    unreachable!()
                };
            }
            _ => panic!("Expected negated integer comparison"),
        }
    }

    #[test]
    fn test_if_then_else_raise_then_sequences_non_constant_else() {
        let x = Ident::create_local("x");
        let if_expr = Lambda::if_(
            Lambda::prim(
                Primitive::Pintcomp(Comparison::Eq),
                vec![Lambda::var(x), Lambda::const_(Constant::int(0))],
                LamLoc::NONE,
            ),
            Lambda::prim(
                Primitive::Praise,
                vec![Lambda::var(Ident::create_local("exn"))],
                LamLoc::NONE,
            ),
            Lambda::static_raise(1, Vec::new()),
        );
        // The constructor keeps the shape; the final pass moves the code.
        assert!(matches!(if_expr, Lambda::LifThenElse(..)));
        let mut a = crate::lambda::arena::LamArena::new();
        let root = a.import(&if_expr);
        let root = crate::lambda::lam_pass_guard_raises::guard_raises(&mut a, root);
        let if_expr = a.export(root);

        match if_expr {
            Lambda::Lsequence(first, second) => {
                assert!(matches!(*second, Lambda::LstaticRaise(1, ref args) if args.is_empty()));
                match *first {
                    Lambda::LifThenElse(_, then_, else_) => {
                        assert!(matches!(
                                                    *then_,
                                                    Lambda::Lprim(__prim100) if matches!(__prim100.as_ref(), PrimInfo {
                                                        primitive: Primitive::Praise,
                                                        ..
                                                    })
                        ));
                        assert!(matches!(
                            *else_,
                            Lambda::Lconst(Constant::JsUndefined { is_unit: true })
                        ));
                    }
                    _ => panic!("Expected rewritten if inside sequence"),
                }
            }
            _ => panic!("Expected raise-then if to lower to sequence"),
        }
    }

    #[test]
    fn test_while_loop() {
        let cond = Lambda::true_();
        let body = Lambda::unit();

        let while_loop = Lambda::while_(cond, body);

        match while_loop {
            Lambda::Lwhile(_, _) => {}
            _ => panic!("Expected Lwhile"),
        }
    }
}

#[cfg(test)]
mod node_size_tests {
    // Every Lambda node is moved and boxed repeatedly by the optimization
    // passes; keep rare large payloads (FFI specs, block runtimes) boxed.
    #[test]
    fn lambda_node_sizes_stay_compact() {
        use std::mem::size_of;
        // Constructor/record block tags and JS call specs are boxed
        // (`ConstructorTag`, `RecordTag`, `RecordInlinedTag`, `JsCall`).
        assert_eq!(size_of::<super::TagInfo>(), 32);
        assert_eq!(size_of::<super::Primitive>(), 40);
        assert_eq!(size_of::<super::arena::PrimPayload>(), 48);
        assert_eq!(size_of::<super::Constant>(), 40);
        assert_eq!(size_of::<super::Lambda>(), 56);
    }
}
