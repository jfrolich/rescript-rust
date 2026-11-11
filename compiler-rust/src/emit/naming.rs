//! First naming slice: collision-free identifiers. Scope collisions fail closed.
//!
//! A globally unique mangled base has the same spelling in every lexical scope,
//! independent of reservation order. Colliding bases need E.3's scoped suffix
//! tables and free-variable reservation pass; they must not be guessed here.
use super::Unsupported;
use crate::ident::Ident;
use crate::js_ir::printer::convert_ident_atom;
use crate::js_ir::walk::{Visitor, walk_block};
use crate::js_ir::{
    ModulePathResolver,
    arena::{Expr, ExprKind, JsArena, JsDepsProgram, VarDecl},
};
use crate::name::Name;
use ahash::AHashMap;

#[derive(Default)]
pub(super) struct Names {
    printed: AHashMap<Ident, Name>,
    owners: AHashMap<Name, Ident>,
    error: Option<Unsupported>,
}
impl Names {
    fn add(&mut self, id: Ident, module: bool) {
        if self.printed.contains_key(&id) {
            return;
        }
        let name = if id.stamp() == 0 && !module {
            id.name_atom()
        } else {
            convert_ident_atom(id.name_atom())
        };
        if let Some(previous) = self.owners.insert(name, id)
            && previous != id
        {
            self.error
                .get_or_insert(Unsupported("scoped identifier collision"));
        }
        // Free stamp-zero globals reserve their converted base inside a
        // function environment even though their uses print the raw JS name.
        if id.stamp() == 0 {
            let reserved = convert_ident_atom(id.name_atom());
            if let Some(previous) = self.owners.insert(reserved, id)
                && previous != id
            {
                self.error
                    .get_or_insert(Unsupported("scoped identifier collision"));
            }
        }
        self.printed.insert(id, name);
    }
    pub(super) fn get(&self, id: &Ident) -> &str {
        &self.printed[id]
    }
    pub(super) fn collect(
        p: &JsDepsProgram,
        resolver: &ModulePathResolver,
    ) -> Result<Self, Unsupported> {
        let mut names = Self::default();
        for module in &p.modules {
            if !module.dynamic_import && resolver.resolve_module_path(module).is_some() {
                names.add(module.id, true);
            }
        }
        for id in &p.program.name_reservations {
            names.add(*id, false);
        }
        walk_block(&mut names, &p.program.arena, &p.program.block);
        for id in &p.program.exports {
            names.add(*id, false);
        }
        match names.error {
            Some(e) => Err(e),
            None => Ok(names),
        }
    }
}
impl Visitor for Names {
    fn visit_expression(&mut self, a: &JsArena, e: Expr) {
        match a.ek(e) {
            ExprKind::Var(id) => self.add(a.ident(id), false),
            ExprKind::Qualified(q) => self.add(a.qual(q).0.id, true),
            ExprKind::Fun(f) => {
                for id in a.ident_slice(a.fun(f).params) {
                    self.add(*id, false);
                }
            }
            _ => {}
        }
    }
    fn visit_declaration(&mut self, _a: &JsArena, decl: &VarDecl) {
        self.add(decl.ident, false);
    }
}
