//! Structural template keys. Locations and arena identities are not part of a key.
use std::io::Write;
use crate::binary_ast::ast_iter::{self, AstIter};
use crate::parse_arena::*;
use crate::parser::ast::*;
use crate::parser::longident::Longident;

// Sorted semantic-name tables: distinct StrIdx values can spell the same name.
// Each entry is sixteen bytes; no hashing or allocation in the visitor.
#[derive(Default)]
struct Names { fields: Vec<(StrIdx, u64)>, constructors: Vec<(StrIdx, u64)>,
    values: Vec<(StrIdx, u64)>, literals: Vec<(StrIdx, u64)>, types: Vec<(StrIdx, u64)> }
impl Names {
    /// O(names log names), once per declaration; sorted Vecs avoid hashing non-unique string handles.
    fn sort(&mut self, arena: &ParseArena) {
        for table in [&mut self.fields, &mut self.constructors, &mut self.values, &mut self.literals, &mut self.types] {
            table.sort_by(|a, b| arena.get_string(a.0).cmp(arena.get_string(b.0)));
            table.dedup_by(|a, b| arena.get_string(a.0) == arena.get_string(b.0));
        }
    }
}
struct Body { bytes: Vec<u8>, nodes: u64, complete: bool }
struct Visitor<'a> { body: &'a mut Body, names: &'a Names }
impl Visitor<'_> {
    /// O(text bytes), append to the single binding buffer; no temporary string allocation.
    fn token(&mut self, text: &str) {
        write!(self.body.bytes, "{}:", text.len()).unwrap();
        self.body.bytes.extend_from_slice(text.as_bytes());
    }
    /// O(encoded scalar size), append directly without an allocated formatted string.
    fn flag(&mut self, flag: impl std::fmt::Debug) { write!(self.body.bytes, "{flag:?};").unwrap(); }
    /// O(log names) string comparisons; no allocations, locks or thread-local access.
    fn name(&mut self, arena: &ParseArena, name: StrIdx, table: &[(StrIdx, u64)]) {
        self.named_text(arena, arena.get_string(name), table);
    }
    /// O(log names) string comparisons; source names can have multiple arena handles.
    fn named_text(&mut self, arena: &ParseArena, text: &str, table: &[(StrIdx, u64)]) {
        if let Ok(i) = table.binary_search_by(|entry| arena.get_string(entry.0).cmp(text)) {
            self.flag(table[i].1);
        } else { self.body.bytes.push(b's'); self.token(text); }
    }
    /// O(path length times log names), traversing borrowed path segments without allocating.
    fn lid(&mut self, arena: &ParseArena, lid: &Longident, table: &[(StrIdx, u64)]) {
        match lid {
            Longident::Lident(name) => { self.body.bytes.push(b'i'); self.name(arena, *name, table); }
            Longident::Ldot(prefix, name) => {
                self.body.bytes.push(b'd'); self.lid(arena, prefix, &[]); self.name(arena, *name, &[]);
            }
            Longident::Lapply(lhs, rhs) => {
                self.body.bytes.push(b'a'); self.lid(arena, lhs, &[]); self.lid(arena, rhs, &[]);
            }
        }
    }
    /// O(log names) comparisons and one scalar tag; no allocation.
    fn label(&mut self, arena: &ParseArena, label: &ArgLabel) {
        self.flag(std::mem::discriminant(label));
        if let Some(name) = label.name_idx() { self.name(arena, name, &[]); }
    }
    /// O(literal bytes + log names); source literals retain their values.
    fn constant(&mut self, arena: &ParseArena, constant: &Constant, generated: bool) {
        self.flag(std::mem::discriminant(constant));
        match constant {
            Constant::Integer(s, suffix) | Constant::Float(s, suffix) => {
                self.token(arena.get_string(*s)); self.flag(suffix);
            }
            Constant::String(StringConst::Valid { semantic, .. }) => self.name(arena, *semantic, if generated { &self.names.literals } else { &[] }),
            Constant::String(StringConst::InvalidSource(source)) => self.token(arena.get_string(*source)),
            Constant::Char { semantic, .. } => self.flag(semantic),
        }
    }
}
impl AstIter for Visitor<'_> {
    /// O(visited subtree occurrences times log names); each child is visited once, no per-node allocation.
    fn expr(&mut self, arena: &ParseArena, idx: ExprIdx) {
        self.body.nodes += 1;
        let desc = &arena.get_expr(idx).pexp_desc;
        self.body.bytes.push(b'E'); self.flag(std::mem::discriminant(desc));
        match desc {
            ExpressionDesc::Pexp_ident(lid) => self.lid(arena, arena.get_longident(lid.txt), &self.names.values),
            ExpressionDesc::Pexp_constant(c) => self.constant(arena, c, arena.loc_ghost(arena.get_expr(idx).pexp_loc)),
            ExpressionDesc::Pexp_let((rec, _, _)) => self.flag(rec),
            ExpressionDesc::Pexp_fun(fun) => {
                self.flag(arena.get_arity(fun.arity)); self.flag(fun.is_async);
                if let Some(params) = arena.stored_nary_fun_params(fun) {
                    self.flag(params.len());
                    for param in params { self.label(arena, &param.p_lbl); self.flag(param.p_default.is_some()); }
                } else { self.flag(1usize); self.label(arena, &fun.arg_label); self.flag(fun.default.is_some()); }
            }
            ExpressionDesc::Pexp_apply(app) => {
                self.flag(app.partial); self.flag(app.transformed_jsx);
                for (label, _) in arena.apply_args(app.args) { self.label(arena, label); }
            }
            ExpressionDesc::Pexp_construct(lid, _) => self.lid(arena, arena.get_longident(lid.txt), &self.names.constructors),
            ExpressionDesc::Pexp_variant(inner) => self.named_text(arena, &inner.0, &self.names.constructors),
            ExpressionDesc::Pexp_record((fields, base)) => {
                self.flag(base.is_some());
                for field in arena.expr_field_list(*fields) {
                    self.lid(arena, arena.get_longident(field.lid.txt), &self.names.fields); self.flag(field.opt);
                }
            }
            ExpressionDesc::Pexp_field(_, lid) => self.lid(arena, arena.get_longident(lid.txt), &self.names.fields),
            ExpressionDesc::Pexp_template(template) => {
                for segment in &template.source_segments { self.name(arena, segment.txt, &self.names.literals); }
            }
            ExpressionDesc::Pexp_ifthenelse(inner) => self.flag(inner.2.is_some()),
            ExpressionDesc::Pexp_tuple(_) | ExpressionDesc::Pexp_array(_) |
            ExpressionDesc::Pexp_match(_) | ExpressionDesc::Pexp_constraint(_) |
            ExpressionDesc::Pexp_sequence(..) | ExpressionDesc::Pexp_ternary(_) => {}
            // Do not silently collapse syntax whose scalar payload is not encoded.
            _ => self.body.complete = false,
        }
        ast_iter::walk_expr(self, arena, idx);
        self.body.bytes.push(b'e');
    }
    /// O(visited subtree occurrences times log names); each child is visited once.
    fn pat(&mut self, arena: &ParseArena, idx: PatIdx) {
        self.body.nodes += 1;
        let desc = &arena.get_pat(idx).ppat_desc;
        self.body.bytes.push(b'P'); self.flag(std::mem::discriminant(desc));
        match desc {
            PatternDesc::Ppat_var(name) | PatternDesc::Ppat_alias(_, name) => self.name(arena, name.txt, &self.names.values),
            PatternDesc::Ppat_constant(c) => self.constant(arena, c, arena.loc_ghost(arena.get_pat(idx).ppat_loc)),
            PatternDesc::Ppat_construct(lid, _) => self.lid(arena, arena.get_longident(lid.txt), &self.names.constructors),
            PatternDesc::Ppat_variant(inner) => self.named_text(arena, &inner.0, &self.names.constructors),
            PatternDesc::Ppat_record(inner) => {
                self.flag(inner.1); self.flag(inner.2.is_some());
                if inner.2.is_some() { self.body.complete = false; }
                for field in arena.pat_field_list(inner.0) {
                    self.lid(arena, arena.get_longident(field.lid.txt), &self.names.fields); self.flag(field.opt);
                }
            }
            PatternDesc::Ppat_any | PatternDesc::Ppat_tuple(_) | PatternDesc::Ppat_array(_) |
            PatternDesc::Ppat_or(..) | PatternDesc::Ppat_constraint(_) | PatternDesc::Ppat_exception(_) => {}
            _ => self.body.complete = false,
        }
        ast_iter::walk_pat(self, arena, idx); self.body.bytes.push(b'p');
    }
    /// O(visited subtree occurrences times log names); each child is visited once.
    fn typ(&mut self, arena: &ParseArena, idx: CoreTypeIdx) {
        self.body.nodes += 1;
        let desc = &arena.get_core_type(idx).ptyp_desc;
        self.body.bytes.push(b'T'); self.flag(std::mem::discriminant(desc));
        match desc {
            CoreTypeDesc::Ptyp_var(name) => self.name(arena, *name, &self.names.types),
            CoreTypeDesc::Ptyp_constr((lid, _)) => self.lid(arena, arena.get_longident(lid.txt), &self.names.types),
            CoreTypeDesc::Ptyp_arrow(inner) => {
                self.label(arena, &inner.0.lbl); self.flag(arena.get_arity(inner.2));
                if inner.0.fixed.is_some() { self.body.complete = false; }
            }
            CoreTypeDesc::Ptyp_any | CoreTypeDesc::Ptyp_tuple(_) => {}
            _ => self.body.complete = false,
        }
        ast_iter::walk_typ(self, arena, idx); self.body.bytes.push(b't');
    }
    /// O(payload occurrences times log names); writes one name and two delimiters.
    fn attribute(&mut self, arena: &ParseArena, attr: &Attribute) {
        self.body.bytes.push(b'A'); self.token(arena.get_string(attr.0.txt));
        self.flag(std::mem::discriminant(&attr.1));
        ast_iter::walk_attribute(self, arena, attr); self.body.bytes.push(b'a');
    }
    /// O(pattern, guard and body occurrences); one visit per child.
    fn case(&mut self, arena: &ParseArena, owner: ExprIdx, index: usize, case: &Case) {
        self.body.bytes.push(b'C'); self.flag(arena.case_guard(owner, index).is_some());
        ast_iter::walk_case(self, arena, owner, index, case); self.body.bytes.push(b'c');
    }
    /// O(item subtree occurrences); unsupported payloads invalidate the key explicitly.
    fn structure_item(&mut self, a: &ParseArena, item: &StructureItem) {
        self.flag(std::mem::discriminant(&item.pstr_desc));
        if !matches!(item.pstr_desc, StructureItemDesc::Pstr_eval(_)) { self.body.complete = false; }
        ast_iter::walk_structure_item(self, a, item);
    }
    /// O(item subtree occurrences); no approximate key is substituted.
    fn signature_item(&mut self, a: &ParseArena, item: &SignatureItem) {
        self.body.complete = false; ast_iter::walk_signature_item(self, a, item);
    }
    /// O(subtree occurrences); no approximate key is substituted.
    fn module_expr(&mut self, a: &ParseArena, i: ModExprIdx) {
        self.body.nodes += 1; self.body.complete = false; ast_iter::walk_module_expr(self, a, i);
    }
    /// O(subtree occurrences); no approximate key is substituted.
    fn module_type(&mut self, a: &ParseArena, i: ModTypeIdx) {
        self.body.nodes += 1; self.body.complete = false; ast_iter::walk_module_type(self, a, i);
    }
}

/// O(attribute count), called once per declaration field or constructor.
fn renamed(attrs: &Attributes, name: &str, arena: &ParseArena) -> bool {
    attrs.iter().any(|a| arena.get_string(a.0.txt) == name)
}
/// O(fields + their attributes): build compact name tables once per declaration.
fn fields(names: &mut Names, fields: &[LabelDeclaration], arena: &mut ParseArena) {
    for field in fields {
        let id = names.fields.len() as u64;
        names.fields.push((field.pld_name.txt, id));
        let variable = arena.intern_string(&format!("spice_field_{}", arena.get_string(field.pld_name.txt)));
        names.values.push((variable, (1 << 32) + id));
        if !renamed(&field.pld_attributes, "spice.key", arena) {
            names.literals.push((field.pld_name.txt, id));
            let path = arena.intern_string(&format!(".{}", arena.get_string(field.pld_name.txt)));
            names.literals.push((path, (1 << 32) + id));
        }
    }
}

/// O(fields log fields + body occurrences log names), with one output buffer per
/// binding, never per visited node. Exact keys are stored rather than hashes;
/// unsupported scalar payloads produce null, never a guessed template identity.
pub(crate) fn record(decl: &TypeDeclaration, group: &[TypeDeclaration], recursive: bool,
    bindings: &[ValueBinding], arena: &mut ParseArena) {
    let Some(mut census) = arena.derived_census.take() else { return; };
    let started = std::time::Instant::now();
    let mut names = Names::default();
    for (i, declaration) in std::iter::once(decl).chain(group.iter().filter(|d| d.ptype_name.txt != decl.ptype_name.txt)).enumerate() {
        names.types.push((declaration.ptype_name.txt, i as u64));
        for (j, suffix) in ["_encode", "_encodeJson", "_decode"].iter().enumerate() {
            let name = arena.intern_string(&format!("{}{suffix}", arena.get_string(declaration.ptype_name.txt)));
            names.values.push((name, (i * 3 + j) as u64));
        }
    }
    for (i, (typ, _)) in decl.ptype_params.iter().enumerate() {
        if let CoreTypeDesc::Ptyp_var(name) = arena.get_core_type(*typ).ptyp_desc {
            names.types.push((name, (1 << 32) + i as u64));
            for (j, prefix) in ["encoder_", "decoder_"].iter().enumerate() {
                let variable = arena.intern_string(&format!("{prefix}{}", arena.get_string(name)));
                names.values.push((variable, (2 << 32) + (i * 2 + j) as u64));
            }
        }
    }
    let class = match &decl.ptype_kind {
        TypeKind::Ptype_record(labels) => { fields(&mut names, labels, arena); "record" }
        TypeKind::Ptype_variant(constructors) => {
            for (i, ctor) in constructors.iter().enumerate() {
                names.constructors.push((ctor.pcd_name.txt, i as u64));
                if !renamed(&ctor.pcd_attributes, "spice.as", arena) { names.literals.push((ctor.pcd_name.txt, (2 << 32) + i as u64)); }
                if let ConstructorArguments::Pcstr_record(labels) = &ctor.pcd_args { fields(&mut names, labels, arena); }
            }
            "variant"
        }
        _ => match decl.ptype_manifest.map(|i| &arena.get_core_type(i).ptyp_desc) {
            Some(CoreTypeDesc::Ptyp_tuple(_)) => "tuple",
            Some(CoreTypeDesc::Ptyp_variant(_)) => "polymorphic_variant",
            Some(CoreTypeDesc::Ptyp_constr(_)) => "constructor_application",
            _ => "other",
        },
    };
    if let Some(manifest) = decl.ptype_manifest {
        if let CoreTypeDesc::Ptyp_variant(inner) = arena.get_core_type(manifest).ptyp_desc.clone() {
            for (i, row) in inner.0.iter().enumerate() {
                if let RowField::Rtag(label, attrs, _, _) = row {
                    let name = arena.intern_string(&label.txt);
                    names.constructors.push((name, i as u64));
                    if !renamed(attrs, "spice.as", arena) { names.literals.push((name, (2 << 32) + i as u64)); }
                }
            }
        }
    }
    names.sort(arena);
    for binding in bindings {
        let mut body = Body { bytes: Vec::new(), nodes: 0, complete: true };
        Visitor { body: &mut body, names: &names }.expr(arena, binding.pvb_expr);
        census.shape_classes.push(class);
        census.shape_nodes.push(body.nodes);
        census.shape_parameterised.push(!decl.ptype_params.is_empty());
        census.shape_recursive.push(recursive);
        census.templates.push(body.complete.then_some(body.bytes));
    }
    census.observer_ns += super::census::nanos(started.elapsed());
    arena.derived_census = Some(census);
}

#[cfg(test)]
mod tests {
    use super::*;
    fn templates(source: &str) -> Vec<Option<Vec<u8>>> {
        let mut parser = crate::parser::Parser::new("shape.res", source);
        let items = crate::parser::module::parse_structure(&mut parser);
        assert!(!parser.has_errors());
        let mut arena = parser.into_arena();
        arena.derived_census = Some(Box::new(super::super::census::Census::new(std::path::Path::new("unused"), "shape.res")));
        for item in &items {
            super::super::expand_structure_item_with_mapper(item, &mut arena, true).unwrap();
        }
        arena.derived_census.unwrap().templates
    }
    #[test]
    fn record_names_normalize_without_renaming_unrelated_locals() {
        let keys = templates("@spice type a = {v: int}\n@spice type b = {other: int}\n");
        assert_eq!(keys.len(), 6);
        assert!(keys.iter().all(Option::is_some));
        assert_eq!(&keys[..3], &keys[3..]);
    }
    #[test]
    fn explicit_keys_and_source_defaults_remain_semantic() {
        let keys = templates("@spice type a = {@spice.key(\"x\") value: int}\n@spice type b = {@spice.key(\"y\") value: int}\n");
        assert_ne!(keys[0], keys[3]);
        let keys = templates("@spice type a = {@spice.default(\"x\") x: string}\n@spice type b = {@spice.default(\"y\") y: string}\n");
        assert_ne!(keys[2], keys[5]);
    }
    #[test]
    fn template_walk_visits_ten_thousand_nodes_once() {
        let source = format!("let xs = [{}]", vec!["0"; 10_000].join(","));
        let mut parser = crate::parser::Parser::new("shape.res", &source);
        let items = crate::parser::module::parse_structure(&mut parser);
        let StructureItemDesc::Pstr_value((_, group)) = items[0].pstr_desc else { panic!() };
        let mut body = Body { bytes: Vec::new(), nodes: 0, complete: true };
        let names = Names::default();
        Visitor { body: &mut body, names: &names }.expr(parser.arena(), parser.arena().vb_list(group)[0].pvb_expr);
        assert_eq!(body.nodes, 10_001);
        assert!(body.complete);
    }
    #[test]
    fn visitor_layout() { assert_eq!(std::mem::size_of::<Visitor<'_>>(), 16); }
}
