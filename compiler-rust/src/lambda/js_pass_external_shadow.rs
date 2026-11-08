//! JS IR pass: rewrite references to externally-shadowed globals.
//!
//! When a top-level `let`/`const` binding shadows a built-in global name
//! (e.g. `let Map = ...`), later references to the *original* global must
//! go through `globalThis.Map` instead of bare `Map`.

use crate::ident::Ident;
use crate::js_ir::arena::{
    Expr, ExprKind, JsArena, JsDepsProgram as DepsProgram, Stmt, StmtKind, VarDecl,
};
use crate::js_ir::build::exp as E;
use crate::js_ir::printer::is_js_keyword_or_global;
use crate::js_ir::walk::{Mapper, Visitor, map_expression_children, map_statement_children};
use crate::lambda::lam_compat::LetKind;
use ahash::AHashSet as HashSet;

pub(crate) fn apply_external_shadow_pass(mut deps: DepsProgram) -> DepsProgram {
    let a = &deps.program.arena;
    let shadowed_globals = deps
        .program
        .block
        .iter()
        .filter_map(|stmt| match a.sk(*stmt) {
            StmtKind::Variable(decl) => {
                let decl = a.var(decl);
                (is_lexical_binding_kind(decl.property) && should_rewrite_binding(&decl.ident))
                    .then(|| decl.ident.name().to_string())
            }
            _ => None,
        })
        .collect::<HashSet<_>>();

    if shadowed_globals.is_empty() {
        return deps;
    }

    // Both rewrites below only replace a reference to a JS global whose name
    // is also the name of a lexical binding (`shadowed_globals` holds the
    // top-level ones; `ShadowedGlobal` runs for every lexical binding at any
    // depth). When no JS global referenced in the program shares a name with
    // any binding, the pass rebuilds the program unchanged, so skip it.
    let mut names = ReferencedNames::default();
    crate::js_ir::walk::walk_block(&mut names, a, &deps.program.block);
    if names
        .globals
        .iter()
        .all(|name| !names.bindings.contains(name))
    {
        return deps;
    }

    let program = &mut deps.program;
    let block = std::mem::take(&mut program.block);
    program.block = GlobalStaticIndex {
        shadowed_globals: &shadowed_globals,
    }
    .block_items(&mut program.arena, &block);
    deps
}

pub(crate) fn is_lexical_binding_kind(property: LetKind) -> bool {
    matches!(
        property,
        LetKind::Strict | LetKind::StrictOpt | LetKind::Alias
    )
}

fn should_rewrite_binding(ident: &Ident) -> bool {
    !ident.is_global() && !is_js_keyword_or_global(ident.name())
}

/// Rewrites `Global.field` to `globalThis.Global.field` for shadowed
/// top-level globals, and references to the global a lexical binding shadows
/// inside its own initializer (`js_pass_external_shadow.ml`).
struct GlobalStaticIndex<'a> {
    shadowed_globals: &'a HashSet<String>,
}

impl Mapper for GlobalStaticIndex<'_> {
    fn statement(&mut self, j: &mut JsArena, stmt: Stmt) -> Stmt {
        let StmtKind::Variable(v) = j.sk(stmt) else {
            return map_statement_children(self, j, stmt);
        };
        let decl = j.var(v).clone();
        let Some(value) = decl.value else {
            return stmt;
        };
        let value = if is_lexical_binding_kind(decl.property) && should_rewrite_binding(&decl.ident)
        {
            ShadowedGlobal {
                name: decl.ident.name(),
            }
            .expression(j, value)
        } else {
            value
        };
        let new_value = self.expression(j, value);
        if Some(new_value) == decl.value {
            return stmt;
        }
        let v = j.var_id(VarDecl {
            value: Some(new_value),
            ..decl
        });
        j.rekind_stmt(stmt, StmtKind::Variable(v))
    }

    fn expression(&mut self, j: &mut JsArena, expr: Expr) -> Expr {
        let expr = map_expression_children(self, j, expr);
        if let ExprKind::StaticIndex(obj, field, pos) = j.ek(expr)
            && let ExprKind::Var(id) = j.ek(obj)
            && let id = j.ident(id)
            && id.is_global()
            && self.shadowed_globals.contains(id.name())
        {
            // `{expr with expression_desc = Static_index (obj, field, pos)}`
            // (js_pass_external_shadow.ml:86) keeps the comment and source
            // location.
            let target = global_this_field(id.name(), j);
            return j.rekind_expr(expr, ExprKind::StaticIndex(target, field, pos));
        }
        expr
    }
}

/// Replaces references to the global `name` with `globalThis.name`,
/// including inside nested functions (`Js_record_map.super`,
/// compiler/core/js_record_map.ml:165-168).
struct ShadowedGlobal<'a> {
    name: &'a str,
}

impl Mapper for ShadowedGlobal<'_> {
    fn expression(&mut self, j: &mut JsArena, expr: Expr) -> Expr {
        let expr = map_expression_children(self, j, expr);
        match j.ek(expr) {
            ExprKind::Var(id) if j.ident(id).is_global() && j.ident(id).name() == self.name => {
                global_this_field(self.name, j)
            }
            _ => expr,
        }
    }
}

fn global_this_field(name: &str, j: &mut JsArena) -> Expr {
    let global_this = E::var(Ident::create_persistent("globalThis"), j);
    E::static_index(global_this, name, None, j)
}

/// Names of the JS globals a program references and of the variables it
/// declares.
#[derive(Default)]
struct ReferencedNames {
    globals: HashSet<&'static str>,
    bindings: HashSet<&'static str>,
}

impl Visitor for ReferencedNames {
    fn visit_expression(&mut self, a: &JsArena, expression: Expr) {
        if let ExprKind::Var(id) = a.ek(expression)
            && a.ident(id).is_global()
        {
            self.globals.insert(a.ident(id).name());
        }
    }

    fn visit_declaration(&mut self, _a: &JsArena, declaration: &VarDecl) {
        self.bindings.insert(declaration.ident.name());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;

    #[test]
    fn shadowed_static_index_keeps_comment() {
        let mut j = JsArena::new();
        let global = Ident::new("Map", 0, IdentFlags::GLOBAL);
        let target = E::var(global, &mut j);
        let expr = E::static_index(target, "size", None, &mut j);
        let expr = E::comment(expr, "note", &mut j);
        let shadowed: HashSet<String> = ["Map".to_string()].into_iter().collect();

        let rewritten = GlobalStaticIndex {
            shadowed_globals: &shadowed,
        }
        .expression(&mut j, expr);

        assert_eq!(j.expr_comment(rewritten), Some("note"));
        let ExprKind::StaticIndex(obj, field, _) = j.ek(rewritten) else {
            panic!("expected a static index");
        };
        assert_eq!(j.text(field), "size");
        assert!(!matches!(j.ek(obj), ExprKind::Var(_)));
    }
}
