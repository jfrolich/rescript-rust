//! `documentSymbol`: a port of analysis/src/document_symbol.ml.

use super::json::Json;
use super::{FileKind, Range};
use crate::binary_ast::ast_iter::{self, AstIter};
use crate::parse_arena::{ExprIdx, LocIdx, ModExprIdx, ParseArena};
use crate::parser::ast::*;
use crate::parser::{Parser, module};

/// `Lsp.Types.SymbolKind`.
#[derive(Debug, Clone, Copy, PartialEq)]
enum SymbolKind {
    Module = 2,
    Property = 7,
    Constructor = 9,
    Function = 12,
    Variable = 13,
    Constant = 14,
    String = 15,
    Number = 16,
    EnumMember = 22,
    TypeParameter = 26,
}

struct Symbol {
    name: String,
    range: Range,
    kind: SymbolKind,
    /// Most recently added last (OCaml's list head).
    children: Option<Vec<Symbol>>,
}

impl Symbol {
    fn to_json(&self) -> Json {
        let range = self.range.to_json();
        let mut fields = Vec::new();
        if let Some(children) = &self.children {
            fields.push((
                "children".to_string(),
                Json::List(children.iter().rev().map(Symbol::to_json).collect()),
            ));
        }
        fields.push(("kind".to_string(), Json::Int(self.kind as i64)));
        fields.push(("name".to_string(), Json::str(&self.name)));
        fields.push(("range".to_string(), range.clone()));
        fields.push(("selectionRange".to_string(), range));
        Json::Assoc(fields)
    }
}

struct Collector {
    symbols: Vec<Symbol>,
}

impl Collector {
    fn add(&mut self, arena: &ParseArena, name: &str, loc: LocIdx, kind: SymbolKind) {
        let location = arena.get_location(loc);
        let start = arena.get_position(location.loc_start);
        let end = arena.get_position(location.loc_end);
        if !location.loc_ghost && start.cnum >= 0 && end.cnum >= 0 {
            self.add_range(name, Range::of_positions(start, end), kind);
        }
    }

    fn add_range(&mut self, name: &str, range: Range, kind: SymbolKind) {
        self.symbols.push(Symbol {
            name: name.to_string(),
            range,
            kind,
            children: None,
        });
    }

    fn type_declaration(&mut self, arena: &ParseArena, td: &TypeDeclaration) {
        self.add(
            arena,
            arena.get_string(td.ptype_name.txt),
            td.ptype_loc,
            SymbolKind::TypeParameter,
        );
        match &td.ptype_kind {
            TypeKind::Ptype_variant(constructors) => {
                for cd in constructors {
                    self.add(
                        arena,
                        arena.get_string(cd.pcd_name.txt),
                        cd.pcd_loc,
                        SymbolKind::EnumMember,
                    );
                }
            }
            TypeKind::Ptype_record(labels) => {
                for ld in labels {
                    self.add(
                        arena,
                        arena.get_string(ld.pld_name.txt),
                        ld.pld_loc,
                        SymbolKind::Property,
                    );
                }
            }
            _ => {}
        }
    }

    fn extension_constructor(&mut self, arena: &ParseArena, ec: &ExtensionConstructor) {
        self.add(
            arena,
            arena.get_string(ec.pext_name.txt),
            ec.pext_loc,
            SymbolKind::Constructor,
        );
    }
}

fn expr_kind(arena: &ParseArena, idx: ExprIdx) -> SymbolKind {
    match &arena.get_expr(idx).pexp_desc {
        ExpressionDesc::Pexp_fun(_) => SymbolKind::Function,
        ExpressionDesc::Pexp_constraint(inner) => expr_kind(arena, inner.0),
        ExpressionDesc::Pexp_constant(constant) => match *constant {
            Constant::String(_) | Constant::Json(_) | Constant::RawSource(_) => SymbolKind::String,
            Constant::Float(..) | Constant::Integer(..) => SymbolKind::Number,
            Constant::Char { .. } => SymbolKind::Constant,
        },
        ExpressionDesc::Pexp_template(_) => SymbolKind::String,
        _ => SymbolKind::Variable,
    }
}

impl AstIter for Collector {
    fn value_binding(&mut self, arena: &ParseArena, vb: &ValueBinding) {
        let pat = arena.get_pat(vb.pvb_pat);
        let name = match &pat.ppat_desc {
            PatternDesc::Ppat_var(name) => Some(name.txt),
            PatternDesc::Ppat_constraint(inner) => match &arena.get_pat(inner.0).ppat_desc {
                PatternDesc::Ppat_var(name) => Some(name.txt),
                _ => None,
            },
            _ => None,
        };
        if let Some(name) = name {
            self.add(
                arena,
                arena.get_string(name),
                vb.pvb_loc,
                expr_kind(arena, vb.pvb_expr),
            );
        }
        ast_iter::walk_value_binding(self, arena, vb);
    }

    fn expr(&mut self, arena: &ParseArena, idx: ExprIdx) {
        let e = arena.get_expr(idx);
        match &e.pexp_desc {
            ExpressionDesc::Pexp_letmodule(letmodule) => {
                let (name, mod_expr, _) = &**letmodule;
                // `{e.pexp_loc with loc_end = mod_expr.pmod_loc.loc_end}`.
                let location = arena.get_location(e.pexp_loc);
                let mod_end = arena
                    .get_location(arena.get_mod_expr(*mod_expr).pmod_loc)
                    .loc_end;
                let start = arena.get_position(location.loc_start);
                let end = arena.get_position(mod_end);
                if !location.loc_ghost && start.cnum >= 0 && end.cnum >= 0 {
                    self.add_range(
                        arena.get_string(name.txt),
                        Range::of_positions(start, end),
                        SymbolKind::Module,
                    );
                }
            }
            ExpressionDesc::Pexp_letexception(letexception) => {
                self.extension_constructor(arena, &letexception.0);
            }
            _ => {}
        }
        ast_iter::walk_expr(self, arena, idx);
    }

    fn structure_item(&mut self, arena: &ParseArena, item: &StructureItem) {
        match &item.pstr_desc {
            StructureItemDesc::Pstr_primitive(vd) => self.add(
                arena,
                arena.get_string(vd.pval_name.txt),
                vd.pval_loc,
                SymbolKind::Variable,
            ),
            StructureItemDesc::Pstr_type(types) => {
                for td in &types.1 {
                    self.type_declaration(arena, td);
                }
            }
            StructureItemDesc::Pstr_module(mb) => self.add(
                arena,
                arena.get_string(mb.pmb_name.txt),
                mb.pmb_loc,
                SymbolKind::Module,
            ),
            StructureItemDesc::Pstr_recmodule(mbs) => {
                for mb in mbs.iter() {
                    self.add(
                        arena,
                        arena.get_string(mb.pmb_name.txt),
                        mb.pmb_loc,
                        SymbolKind::Module,
                    );
                }
            }
            StructureItemDesc::Pstr_exception(ec) => self.extension_constructor(arena, ec),
            _ => {}
        }
        ast_iter::walk_structure_item(self, arena, item);
    }

    fn signature_item(&mut self, arena: &ParseArena, item: &SignatureItem) {
        match &item.psig_desc {
            SignatureItemDesc::Psig_value(vd) => self.add(
                arena,
                arena.get_string(vd.pval_name.txt),
                vd.pval_loc,
                SymbolKind::Variable,
            ),
            SignatureItemDesc::Psig_type(types) => {
                for td in &types.1 {
                    self.type_declaration(arena, td);
                }
            }
            SignatureItemDesc::Psig_module(md) => self.add(
                arena,
                arena.get_string(md.pmd_name.txt),
                md.pmd_loc,
                SymbolKind::Module,
            ),
            SignatureItemDesc::Psig_recmodule(mds) => {
                for md in mds.iter() {
                    self.add(
                        arena,
                        arena.get_string(md.pmd_name.txt),
                        md.pmd_loc,
                        SymbolKind::Module,
                    );
                }
            }
            SignatureItemDesc::Psig_exception(ec) => self.extension_constructor(arena, ec),
            _ => {}
        }
        ast_iter::walk_signature_item(self, arena, item);
    }

    fn module_expr(&mut self, arena: &ParseArena, idx: ModExprIdx) {
        match &arena.get_mod_expr(idx).pmod_desc {
            // Don't double-list items in implementation and interface.
            ModuleExprDesc::Pmod_constraint(mod_expr, _) => {
                ast_iter::walk_module_expr(self, arena, *mod_expr)
            }
            _ => ast_iter::walk_module_expr(self, arena, idx),
        }
    }
}

/// `Document_symbol.get_symbols`, as JSON.
pub fn get_symbols(source: &str, kind: FileKind) -> Json {
    let mut collector = Collector {
        symbols: Vec::new(),
    };
    let mut parser = Parser::new("", source);
    match kind {
        FileKind::Res => {
            let structure = module::parse_structure(&mut parser);
            ast_iter::walk_structure(&mut collector, parser.arena(), &structure);
        }
        FileKind::Resi => {
            let signature = module::parse_signature(&mut parser);
            ast_iter::walk_signature(&mut collector, parser.arena(), &signature);
        }
    }
    // `!symbols` is newest first; `List.sort` is stable.
    let mut symbols = collector.symbols;
    symbols.reverse();
    symbols.sort_by_key(|s| s.range.key());
    let mut roots: Vec<Symbol> = Vec::new();
    for symbol in symbols {
        add_symbol_to_children(symbol, &mut roots);
    }
    Json::List(roots.iter().rev().map(Symbol::to_json).collect())
}

/// `add_symbol_to_children`, with the list head at the end of `children`.
fn add_symbol_to_children(symbol: Symbol, children: &mut Vec<Symbol>) {
    match children.last_mut() {
        Some(last) if symbol.range.is_inside(&last.range) => {
            add_symbol_to_children(symbol, last.children.get_or_insert_with(Vec::new));
        }
        _ => children.push(symbol),
    }
}
