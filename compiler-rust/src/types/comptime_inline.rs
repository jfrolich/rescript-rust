//! @comptime.inline — run ReScript functions in a JS engine (Boa) at compile time.
//!
//! Unlike @comptime which partial-evaluates the typed tree, @comptime.inline
//! takes a fully runtime-capable function and runs it in an embedded JS engine
//! when all its arguments are compile-time constants.
//!
//! Usage:
//!   @comptime.inline
//!   let capitalize = (s: string): string =>
//!     s->String.charAt(0)->String.toUpperCase ++ s->String.sliceToEnd(~start=1)
//!
//! When called as `capitalize("alice")` in a comptime context, the function
//! is compiled to JS, evaluated in Boa, and the result "Alice" is substituted
//! at the call site.

use crate::types::comptime::ComptimeValue;

/// Result of evaluating an @comptime.inline call.
#[derive(Debug, Clone)]
pub enum InlineEvalResult {
    Value(ComptimeValue),
    Error(String),
}

/// Evaluate a JS program (containing the function definition plus a call)
/// and return the result as a ComptimeValue.
#[cfg(feature = "comptime-inline")]
pub fn evaluate_js(source: &str) -> InlineEvalResult {
    use boa_engine::{Context, Source};

    let mut ctx = Context::default();
    let result = ctx.eval(Source::from_bytes(source.as_bytes()));

    match result {
        Ok(val) => {
            if val.is_string() {
                let js_str = val.to_string(&mut ctx).unwrap();
                let s = js_str.to_std_string().unwrap_or_default();
                InlineEvalResult::Value(ComptimeValue::String(s))
            } else if val.is_number() {
                let f = val.to_number(&mut ctx).unwrap_or(0.0);
                if f.fract() == 0.0 && f.abs() < (i64::MAX as f64) {
                    InlineEvalResult::Value(ComptimeValue::Int(f as i64))
                } else {
                    InlineEvalResult::Value(ComptimeValue::Float(f))
                }
            } else if val.is_boolean() {
                InlineEvalResult::Value(ComptimeValue::Bool(val.to_boolean()))
            } else if val.is_null() || val.is_undefined() {
                InlineEvalResult::Value(ComptimeValue::Unit)
            } else {
                InlineEvalResult::Error("@comptime.inline: unsupported result type".to_string())
            }
        }
        Err(e) => InlineEvalResult::Error(format!("JS eval error: {}", e)),
    }
}

#[cfg(not(feature = "comptime-inline"))]
pub fn evaluate_js(_source: &str) -> InlineEvalResult {
    InlineEvalResult::Error(
        "@comptime.inline not available: compile with --features comptime-inline".to_string(),
    )
}

/// Format a ComptimeValue as a JS literal (for argument serialization).
pub fn comptime_value_to_js_literal(val: &ComptimeValue) -> Option<String> {
    match val {
        ComptimeValue::Int(n) => Some(n.to_string()),
        ComptimeValue::Float(f) => Some(f.to_string()),
        ComptimeValue::String(s) => Some(format!("{:?}", s)),
        ComptimeValue::Bool(b) => Some(b.to_string()),
        ComptimeValue::Unit => Some("undefined".to_string()),
        _ => None,
    }
}

/// Translate a simple ReScript parse-tree expression to JavaScript source.
/// Supports: string literals, int/float/bool constants, variable refs,
/// string concatenation (++), arithmetic, basic function application
/// (to stdlib String/Int/... methods mapped to JS equivalents).
///
/// Returns None if the expression contains unsupported constructs.
pub fn translate_simple_expr_to_js(
    expr: &crate::parser::ast::Expression,
    arena: &crate::parse_arena::ParseArena,
) -> Option<String> {
    use crate::parser::ast::ExpressionDesc as ED;
    match &*expr.pexp_desc {
        ED::Pexp_constant(c) => match &**c {
            crate::parser::ast::Constant::String(s) => Some(format!("{:?}", s.semantic())),
            crate::parser::ast::Constant::Integer(s, _) => Some(s.to_string()),
            crate::parser::ast::Constant::Float(s, _) => Some(s.to_string()),
            _ => None,
        },
        ED::Pexp_ident(lid) => {
            let longident = arena.get_longident(lid.txt);
            if longident.is_simple() {
                Some(arena.get_string(longident.last_idx()).to_string())
            } else {
                // Module path like String.toUpperCase — translate common ones
                let parts: Vec<String> = longident
                    .flatten_idx()
                    .iter()
                    .map(|idx| arena.get_string(*idx).to_string())
                    .collect();
                match parts.as_slice() {
                    [a] => Some(a.clone()),
                    [module, name] => {
                        // Map ReScript stdlib to JS equivalents for common ops
                        match (module.as_str(), name.as_str()) {
                            ("String", "toUpperCase") => Some("((s)=>s.toUpperCase())".into()),
                            ("String", "toLowerCase") => Some("((s)=>s.toLowerCase())".into()),
                            ("String", "length") => Some("((s)=>s.length)".into()),
                            ("String", "concat") => Some("((a,b)=>a+b)".into()),
                            ("String", "trim") => Some("((s)=>s.trim())".into()),
                            ("Int", "toString") => Some("((n)=>String(n))".into()),
                            ("Float", "toString") => Some("((n)=>String(n))".into()),
                            _ => None,
                        }
                    }
                    _ => None,
                }
            }
        }
        ED::Pexp_apply(inner) => {
            let crate::parser::ast::PexpApply { funct, args, .. } = &**inner;
            let funct_expr = arena.get_expr(*funct);
            let funct_js = translate_simple_expr_to_js(funct_expr, arena)?;
            let args_js: Option<Vec<String>> = args
                .iter()
                .map(|(_label, arg_idx)| {
                    let arg_expr = arena.get_expr(*arg_idx);
                    translate_simple_expr_to_js(arg_expr, arena)
                })
                .collect();
            let args_js = args_js?;

            // Special-case string concat operator `++`
            if funct_js == "++" && args_js.len() == 2 {
                return Some(format!("({} + {})", args_js[0], args_js[1]));
            }

            Some(format!("{}({})", funct_js, args_js.join(", ")))
        }
        ED::Pexp_fun(inner) => {
            let pat = arena.get_pat(inner.lhs);
            let param_name = match &*pat.ppat_desc {
                crate::parser::ast::PatternDesc::Ppat_var(nl) => {
                    arena.get_string(nl.txt).to_string()
                }
                crate::parser::ast::PatternDesc::Ppat_constraint(inner_box) => {
                    let (inner_pat_idx, _) = &**inner_box;
                    let inner_pat = arena.get_pat(*inner_pat_idx);
                    if let crate::parser::ast::PatternDesc::Ppat_var(nl) = &*inner_pat.ppat_desc {
                        arena.get_string(nl.txt).to_string()
                    } else {
                        return None;
                    }
                }
                _ => return None,
            };
            let body = arena.get_expr(inner.rhs);
            let body_js = translate_simple_expr_to_js(body, arena)?;
            Some(format!("(({}) => ({}))", param_name, body_js))
        }
        ED::Pexp_constraint(inner) => {
            let (expr_idx, _) = &**inner;
            translate_simple_expr_to_js(arena.get_expr(*expr_idx), arena)
        }
        _ => None,
    }
}
