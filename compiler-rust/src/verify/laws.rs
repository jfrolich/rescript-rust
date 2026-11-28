//! `@law` (docs/verify/law.md): a property of the program, written as a
//! function that returns `bool` for every value of its parameters.
//!
//! A law is type checked and checked for purity in every build, and is no
//! part of the program: nothing can refer to it, and the build leaves it out
//! of the JavaScript. `rescript verify` compiles the file with its laws kept
//! and runs each on values made from its parameter types, which this module
//! describes.

use serde_json::{Value, json};

use super::purity::Diagnostic;
use super::shape::{self, Definitions};
use crate::parse_arena::ParseArena;
use crate::parser::ast::Attributes;
use crate::types::context::TypeContext;
use crate::types::tast_iterator::TastIterator;
use crate::types::type_expr::TypeDesc;
use crate::types::typedtree::*;
use crate::types::{TypeExprRef, predef};

/// The attribute that marks a law.
pub const LAW: &str = "law";

/// Whether a binding's attributes mark it as a check: it is no part of the
/// program.
pub fn is_check(arena: &ParseArena, attributes: &Attributes) -> bool {
    attributes
        .iter()
        .any(|(name, _)| super::is_check_attribute(arena.get_string(name.txt)))
}

fn has_attribute(arena: &ParseArena, attributes: &Attributes, wanted: &str) -> bool {
    attributes
        .iter()
        .any(|(name, _)| arena.get_string(name.txt) == wanted)
}

/// A check of a file, as `rescript verify` runs it.
#[derive(Debug, Clone)]
pub struct Item {
    /// `"law"` or `"spec"`.
    pub kind: &'static str,
    /// The modules of the file the check is in, then its name: the path of
    /// its export in the file compiled with checks kept.
    pub path: Vec<String>,
    /// The line of the check, 0 when the file was parsed without locations.
    pub line: u32,
    /// What the runner needs besides the exported value.
    pub detail: Value,
}

impl Item {
    /// The item as the runner reads it.
    pub fn to_json(&self) -> Value {
        json!({
            "kind": self.kind,
            "path": self.path,
            "line": self.line,
            "detail": self.detail,
        })
    }
}

pub(super) struct Collector<'a> {
    pub(super) ctx: &'a TypeContext,
    pub(super) ta: &'a TypedArena,
    pub(super) arena: &'a ParseArena,
    items: Vec<Item>,
    diagnostics: Vec<Diagnostic>,
    /// The expressions of the checks found where a check may be.
    placed: Vec<TExprIdx>,
    /// Whether to try to prove each law, as `rescript verify` does.
    prove: bool,
    structure: &'a Structure,
    /// The file's bindings, once a law needed them.
    index: Option<super::purity::Index>,
    /// The laws proved so far: later ones may use them.
    lemmas: Vec<super::prove::Lemma>,
}

/// Whether a law is marked `@law(proved)`: it must be proved, not only run.
fn wants_proof(arena: &ParseArena, attributes: &Attributes) -> bool {
    use crate::parser::ast::{
        ExpressionDesc as Parsed, Payload as Written, StructureItemDesc as Item,
    };
    use crate::parser::longident::Longident;
    attributes.iter().any(|(name, payload)| {
        arena.get_string(name.txt) == LAW
            && match payload {
                Written::PStr(items) if items.len() == 1 => match &items[0].pstr_desc {
                    Item::Pstr_eval(eval) => match &arena.get_expr(eval.0).pexp_desc {
                        Parsed::Pexp_ident(lid) => matches!(
                            arena.get_longident(lid.txt),
                            Longident::Lident(word) if arena.get_string(*word) == "proved"
                        ),
                        _ => false,
                    },
                    _ => false,
                },
                _ => false,
            }
    })
}

/// The checks of a type checked implementation, and what is wrong with the
/// ones that cannot be run. Cost: one walk of the typed tree; only called
/// for a file the parser saw a check attribute in.
pub fn collect(
    ctx: &TypeContext,
    ta: &TypedArena,
    arena: &ParseArena,
    structure: &Structure,
    prove: bool,
) -> (Vec<Item>, Vec<Diagnostic>) {
    let mut collector = Collector {
        ctx,
        ta,
        arena,
        items: Vec::new(),
        diagnostics: Vec::new(),
        placed: Vec::new(),
        prove,
        structure,
        index: None,
        lemmas: Vec::new(),
    };
    collector.structure(structure, &mut Vec::new());
    let mut misplaced = Misplaced {
        ta,
        arena,
        placed: &collector.placed,
        found: Vec::new(),
    };
    TastIterator::structure(&mut misplaced, structure);
    for loc in misplaced.found {
        collector.diagnostics.push(Diagnostic {
            loc: arena.to_location(loc),
            message: "A law or spec must be a `let` at the top level of a file, or of a module written as `module M = { ... }` in it.\n\n\
                      Here nothing could run it: the build leaves checks out of the program."
                .to_string(),
        });
    }
    (collector.items, collector.diagnostics)
}

impl Collector<'_> {
    fn structure(&mut self, structure: &Structure, modules: &mut Vec<String>) {
        let ta = self.ta;
        for item in ta.structure_items(structure.str_items) {
            match &item.str_desc {
                StructureItemDesc::Tstr_value(_, bindings) => {
                    let bindings = ta.value_bindings(*bindings);
                    for binding in bindings {
                        if !is_check(self.arena, &binding.vb_attributes) {
                            continue;
                        }
                        self.placed.push(binding.vb_expr);
                        if bindings.len() != 1 {
                            self.report(
                                binding.vb_loc,
                                "A law or spec is a `let` of its own: it cannot be one of several bindings joined by `and`.".to_string(),
                            );
                            continue;
                        }
                        self.check(binding, modules);
                    }
                }
                StructureItemDesc::Tstr_module(binding) => {
                    // The module's values are exported as written only when
                    // nothing stands between the name and the structure.
                    if let ModuleExprDesc::Tmod_structure(inner) =
                        &ta.module_expr(binding.mb_expr).mod_desc
                    {
                        modules.push(binding.mb_id.name().to_string());
                        self.structure(inner, modules);
                        modules.pop();
                    }
                }
                _ => {}
            }
        }
    }

    pub(super) fn report(&mut self, loc: crate::parse_arena::LocIdx, message: String) {
        self.diagnostics.push(Diagnostic {
            loc: self.arena.to_location(loc),
            message,
        });
    }

    fn check(&mut self, binding: &ValueBinding, modules: &[String]) {
        let ta = self.ta;
        let name = match &ta.pattern(binding.vb_pat).pat_desc {
            PatternDesc::Tpat_var(id, _) => id.name(),
            // `let name: t = ...` is typed as `(_: t) as name`.
            PatternDesc::Tpat_alias(inner, id, _)
                if matches!(ta.pattern(*inner).pat_desc, PatternDesc::Tpat_any) =>
            {
                id.name()
            }
            _ => {
                self.report(
                    ta.pattern(binding.vb_pat).pat_loc,
                    "A law or spec needs a name: bind it to a single name.".to_string(),
                );
                return;
            }
        };
        let mut path: Vec<String> = modules.to_vec();
        path.push(name.to_string());
        let line = self.arena.to_location(binding.vb_loc).loc_start.line.max(0) as u32;
        if has_attribute(self.arena, &binding.vb_attributes, LAW) {
            if let Some(detail) = self.law(name, binding) {
                self.items.push(Item {
                    kind: "law",
                    path,
                    line,
                    detail,
                });
            }
        } else if has_attribute(self.arena, &binding.vb_attributes, super::specs::SPEC)
            && let Some(detail) = self.spec(name, binding)
        {
            self.items.push(Item {
                kind: "spec",
                path,
                line,
                detail,
            });
        }
    }

    /// The parameters of a law, when it is one that can be run.
    fn law(&mut self, name: &str, binding: &ValueBinding) -> Option<Value> {
        let ta = self.ta;
        let ctx = self.ctx;
        let value = ta.expr(binding.vb_expr);
        let ExpressionDesc::Texp_function { params, body, .. } = &value.exp_desc else {
            self.report(
                value.exp_loc,
                format!(
                    "A law is a function that returns `bool`: `let {name} = (a, b) => ...`.\n\n\
                     It is run on values made from the types of its parameters."
                ),
            );
            return None;
        };
        let env = ctx.get_typed_env(value.exp_env)?;
        let result = ta.expr(*body);
        if !is_bool(ctx, &env, result.exp_type) {
            self.report(
                result.exp_loc,
                format!(
                    "A law returns `bool`: whether the property holds for the values it was given. `{name}` returns something else.\n\n\
                     When a law has several parameters, write them as one function: `(a, b) => ...`."
                ),
            );
            return None;
        }
        let mut definitions = Definitions::default();
        let mut parameters = Vec::new();
        let mut ok = true;
        for (position, param) in ta.function_params(*params).iter().enumerate() {
            let pattern = ta.pattern(param.fp_pat);
            let written = match &pattern.pat_desc {
                PatternDesc::Tpat_var(id, _) => id.name().to_string(),
                PatternDesc::Tpat_alias(_, id, _) => id.name().to_string(),
                _ => format!("argument {}", position + 1),
            };
            match shape::of_type(ctx, &env, pattern.pat_type, &mut definitions) {
                Ok(shape) => parameters.push(json!({ "name": written, "shape": shape })),
                Err(shape::Unsupported(reason)) => {
                    ok = false;
                    self.report(
                        pattern.pat_loc,
                        format!(
                            "No value can be made for `{written}`: {reason}.\n\n\
                             A law is run on values made from the types of its parameters. Take what this value is built from as the parameter, and build the value in the law."
                        ),
                    );
                }
            }
        }
        if !ok {
            return None;
        }
        // A proof is for every value; a run is for the values it made.
        let proof = self.prove.then(|| {
            let index = self
                .index
                .get_or_insert_with(|| super::purity::index(ta, self.arena, self.structure));
            let shapes: Vec<Value> = parameters.iter().map(|p| p["shape"].clone()).collect();
            let names: Vec<String> = parameters
                .iter()
                .map(|p| p["name"].as_str().unwrap_or_default().to_string())
                .collect();
            let proof = super::prove::prove(
                ctx,
                ta,
                index,
                definitions.clone(),
                binding.vb_expr,
                &names,
                &shapes,
                &self.lemmas,
            );
            if proof["status"] == "proved" {
                self.lemmas.push(super::prove::Lemma {
                    name: name.to_string(),
                    expr: binding.vb_expr,
                    shapes,
                });
            }
            proof
        });
        let mut detail = json!({ "params": parameters, "defs": definitions.into_json() });
        if let Some(proof) = proof {
            detail["proof"] = proof;
        }
        if wants_proof(self.arena, &binding.vb_attributes) {
            detail["must"] = json!(true);
        }
        Some(detail)
    }
}

fn is_bool(ctx: &TypeContext, env: &crate::types::Env, ty: TypeExprRef) -> bool {
    let ty = crate::types::ctype::expand_head(ctx, env, ty);
    matches!(
        &*ctx.borrow_desc(ctx.repr(ty)),
        TypeDesc::Tconstr { path, .. } if path.same(&predef::path_bool())
    )
}

/// Finds the checks that are not where one may be.
struct Misplaced<'a> {
    ta: &'a TypedArena,
    arena: &'a ParseArena,
    placed: &'a [TExprIdx],
    found: Vec<crate::parse_arena::LocIdx>,
}

impl<'a> TastIterator<'a> for Misplaced<'a> {
    fn arena(&self) -> &'a TypedArena {
        self.ta
    }

    fn value_binding(&mut self, binding: &ValueBinding) {
        if is_check(self.arena, &binding.vb_attributes) && !self.placed.contains(&binding.vb_expr) {
            self.found.push(binding.vb_loc);
        }
        self.pat(self.ta.pattern(binding.vb_pat));
        self.expr(self.ta.expr(binding.vb_expr));
    }
}
