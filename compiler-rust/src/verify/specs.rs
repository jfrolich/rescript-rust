//! `@spec` (docs/verify/spec.md): a state machine and what must be true of
//! it, written as a `Spec.t<state, action>` (`Stdlib_Spec.res`).
//!
//! A spec is a check like a law: type checked and checked for purity in
//! every build, and no part of the program. `rescript verify` compiles the
//! file with it kept and goes through every state the machine can get into.
//! This module says what the runner needs for that: how to print a state and
//! an action, and which actions there are when the spec does not say.

use serde_json::{Value, json};

use super::laws::Collector;
use super::shape::{self, Definitions};
use crate::types::type_expr::TypeDesc;
use crate::types::typedtree::*;
use crate::types::{Env, TypeExprRef};

/// The attribute that marks a spec.
pub const SPEC: &str = "spec";

/// The fields of a spec that say what to check.
const PROPERTIES: [&str; 4] = ["always", "sometimes", "reachable", "eventually"];

/// The most actions a spec without `actions` can have: each is tried in
/// every state.
const ACTION_LIMIT: u64 = 10_000;

impl Collector<'_> {
    /// What the runner needs to check a spec, when it is one that can be.
    pub(super) fn spec(&mut self, name: &str, binding: &ValueBinding) -> Option<Value> {
        let ta = self.ta;
        let ctx = self.ctx;
        let value = ta.expr(binding.vb_expr);
        let env = ctx.get_typed_env(value.exp_env)?;
        let Some((state, action)) = machine_types(ctx, &env, value.exp_type) else {
            self.report(
                value.exp_loc,
                format!(
                    "A spec is a `Spec.t<state, action>`: the state a machine starts in, its reducer, and what must be true of it.\n\n\
                     Write `let {name}: Spec.t<state, action> = {{init: ..., step: ..., always: state => ...}}`."
                ),
            );
            return None;
        };

        // Which fields the spec has is known when it is written out.
        let written: Option<Vec<&str>> = match &value.exp_desc {
            ExpressionDesc::Texp_record {
                fields,
                extended_expression: None,
                ..
            } => Some(
                ta.record_fields(*fields)
                    .iter()
                    .map(|(label, _, _)| label.lbl_name.as_str())
                    .collect(),
            ),
            _ => None,
        };
        if let Some(written) = &written
            && !PROPERTIES.iter().any(|property| written.contains(property))
        {
            self.report(
                value.exp_loc,
                format!(
                    "The spec `{name}` checks nothing.\n\n\
                     Say what must be true of the machine with `always`, `sometimes`, `reachable` or `eventually`: each is a function from a state to `bool`."
                ),
            );
            return None;
        }

        let mut definitions = Definitions::default();
        let state = shape::for_printing(ctx, &env, state, &mut definitions);
        let actions = match &written {
            Some(written) if written.contains(&"actions") => "given",
            Some(_) => "all",
            None => "unknown",
        };
        let action = if actions == "all" {
            // Every value of the action type happens in every state.
            let listed = shape::of_type(ctx, &env, action, &mut definitions).and_then(|shape| {
                match definitions.count(&shape, ACTION_LIMIT) {
                    Some(_) => Ok(shape),
                    None => Err(shape::Unsupported(
                        "the type has too many values: each would be tried in every state"
                            .to_string(),
                    )),
                }
            });
            match listed {
                Ok(shape) => shape,
                Err(shape::Unsupported(reason)) => {
                    self.report(
                        value.exp_loc,
                        format!(
                            "The actions of the spec `{name}` cannot be listed: {reason}.\n\n\
                             A spec without `actions` tries every value of its action type in every state. Give this one `actions: state => [...]`: the actions that can happen in a state."
                        ),
                    );
                    return None;
                }
            }
        } else {
            shape::for_printing(ctx, &env, action, &mut definitions)
        };
        Some(json!({
            "state": state,
            "action": action,
            "actions": actions,
            "defs": definitions.into_json(),
        }))
    }
}

/// The state and action types of a `Spec.t<state, action>`.
fn machine_types(
    ctx: &crate::types::context::TypeContext,
    env: &Env,
    ty: TypeExprRef,
) -> Option<(TypeExprRef, TypeExprRef)> {
    let ty = crate::types::ctype::expand_head(ctx, env, ty);
    match &*ctx.borrow_desc(ctx.repr(ty)) {
        TypeDesc::Tconstr { path, args, .. }
            if env.normalize_path(ctx, path).name_eq("Stdlib_Spec.t") =>
        {
            let mut args = ctx.type_list(*args).iter();
            Some((args.next()?, args.next()?))
        }
        _ => None,
    }
}
