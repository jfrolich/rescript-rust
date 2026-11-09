//! Raw node builders shared by the JS IR unit tests.

use super::arena::{Expr, ExprKind, FunInfo, JsArena, PropList, PropName, Stmt};
use super::build::stmt as JS;
use super::op::PropertyName;
use crate::ident::Ident;

/// A function expression node, built raw (no smart-constructor folding).
pub(crate) fn test_fun(
    is_method: bool,
    params: &[Ident],
    body: &[Stmt],
    return_unit: bool,
    async_: bool,
    directive: Option<&str>,
    j: &mut JsArena,
) -> Expr {
    let params = j.ident_list(params);
    let body = JS::list(body, j);
    let directive = directive.map(|d| j.str(d));
    let f = j.fun_id(FunInfo {
        is_method,
        params,
        body,
        return_unit,
        async_,
        directive,
    });
    j.expr(ExprKind::Fun(f))
}

/// Object-literal properties for `ExprKind::Object`.
pub(crate) fn test_props(props: Vec<(PropertyName, Expr)>, j: &mut JsArena) -> PropList {
    let props: Vec<(PropName, Expr)> = props
        .into_iter()
        .map(|(name, value)| match name {
            PropertyName::Lit(s) => (PropName::Lit(j.str(&s)), value),
            PropertyName::Symbol => (PropName::Symbol, value),
        })
        .collect();
    j.prop_list(&props)
}
