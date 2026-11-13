//! Structural template keys. Locations and arena identities are not part of a key.
use std::io::Write;
use crate::binary_ast::ast_iter::{self, AstIter};
use crate::parse_arena::*;
use crate::parser::ast::*;
use crate::parser::longident::Longident;

// Semantic names can have multiple arena handles. Compare borrowed spellings,
// including virtual affixes, rather than allocating generated-name strings.
#[derive(Clone, Copy)]
enum Spelling { Plain, Field, Path, Encode, EncodeJson, Decode, Encoder, Decoder }
impl Spelling {
    /// O(1): select static affixes; no formatting or interning.
    fn affixes(self) -> (&'static str, &'static str) {
        match self {
            Self::Plain => ("", ""), Self::Field => ("spice_field_", ""),
            Self::Path => (".", ""), Self::Encode => ("", "_encode"),
            Self::EncodeJson => ("", "_encodeJson"), Self::Decode => ("", "_decode"),
            Self::Encoder => ("encoder_", ""), Self::Decoder => ("decoder_", ""),
        }
    }
}
struct Name<'a> { text: &'a str, id: u64, spelling: Spelling }
impl<'a> Name<'a> {
    /// O(1): borrow a source spelling and attach a virtual affix.
    fn new(text: &'a str, id: u64, spelling: Spelling) -> Self { Self { text, id, spelling } }
    /// O(1) construction; O(spelling bytes) to exhaust, with no allocation.
    fn bytes(&self) -> impl Iterator<Item = u8> + '_ {
        let (prefix, suffix) = self.spelling.affixes();
        prefix.bytes().chain(self.text.bytes()).chain(suffix.bytes())
    }
}
#[derive(Default)]
struct Names<'a> { fields: Vec<Name<'a>>, constructors: Vec<Name<'a>>,
    values: Vec<Name<'a>>, literals: Vec<Name<'a>>, types: Vec<Name<'a>> }
impl Names<'_> {
    /// O(names log names * spelling bytes), once per declaration; no string allocation.
    fn sort(&mut self) { self.sort_with(|a, b| a.bytes().cmp(b.bytes())); }
    /// O(names log names) comparisons plus a linear deduplication. The comparator
    /// is specialized away in production; tests count its actual invocations.
    fn sort_with(&mut self, mut cmp: impl FnMut(&Name<'_>, &Name<'_>) -> std::cmp::Ordering) {
        for table in [&mut self.fields, &mut self.constructors, &mut self.values, &mut self.literals, &mut self.types] {
            table.sort_by(&mut cmp);
            table.dedup_by(|a, b| cmp(a, b).is_eq());
        }
    }
}
struct Body { bytes: Vec<u8>, nodes: u64, complete: bool }
struct Visitor<'a, 'source> { body: &'a mut Body, names: &'a Names<'source> }
impl Visitor<'_, '_> {
    /// O(text bytes), append to the single binding buffer; no temporary string allocation.
    fn token(&mut self, text: &str) {
        write!(self.body.bytes, "{}:", text.len()).unwrap();
        self.body.bytes.extend_from_slice(text.as_bytes());
    }
    /// O(encoded scalar size), append directly without an allocated formatted string.
    fn flag(&mut self, flag: impl std::fmt::Debug) { write!(self.body.bytes, "{flag:?};").unwrap(); }
    /// O(log names * spelling bytes) comparisons; no allocations, locks or thread-local access.
    fn name(&mut self, arena: &ParseArena, name: StrIdx, table: &[Name<'_>]) {
        self.named_text(arena, arena.get_string(name), table);
    }
    /// O(log names * spelling bytes) comparisons; source names can have multiple arena handles.
    fn named_text(&mut self, _arena: &ParseArena, text: &str, table: &[Name<'_>]) {
        if let Ok(i) = table.binary_search_by(|entry| entry.bytes().cmp(text.bytes())) {
            self.flag(table[i].id);
        } else { self.body.bytes.push(b's'); self.token(text); }
    }
    /// O(path length times log names), traversing borrowed path segments without allocating.
    fn lid(&mut self, arena: &ParseArena, lid: &Longident, table: &[Name<'_>]) {
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
    /// O(log names * spelling bytes) comparisons and one scalar tag; no allocation.
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
impl AstIter for Visitor<'_, '_> {
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
fn fields<'a>(names: &mut Names<'a>, fields: &[LabelDeclaration], arena: &'a ParseArena) {
    for field in fields {
        let id = names.fields.len() as u64;
        let text = arena.get_string(field.pld_name.txt);
        names.fields.push(Name::new(text, id, Spelling::Plain));
        names.values.push(Name::new(text, (1 << 32) + id, Spelling::Field));
        if !renamed(&field.pld_attributes, "spice.key", arena) {
            names.literals.push(Name::new(text, id, Spelling::Plain));
            names.literals.push(Name::new(text, (1 << 32) + id, Spelling::Path));
        }
    }
}

/// O(names log names * spelling bytes + body occurrences * lookup cost), where
/// names include fields, constructors, parameters and declarations in the group.
/// Attribute inspection is linear in their count. One output buffer per
/// binding, never per visited node. Exact keys are stored rather than hashes;
/// unsupported scalar payloads produce null, never a guessed template identity.
pub(crate) fn record(decl: &TypeDeclaration, group: &[TypeDeclaration], recursive: bool,
    bindings: &[ValueBinding], arena: &mut ParseArena) {
    if bindings.is_empty() { return; }
    let Some(mut census) = arena.derived_census.take() else { return; };
    let started = std::time::Instant::now();
    let mut names = Names::default();
    for (i, declaration) in std::iter::once(decl).chain(group.iter().filter(|d| d.ptype_name.txt != decl.ptype_name.txt)).enumerate() {
        let text = arena.get_string(declaration.ptype_name.txt);
        names.types.push(Name::new(text, i as u64, Spelling::Plain));
        for (j, spelling) in [Spelling::Encode, Spelling::EncodeJson, Spelling::Decode].into_iter().enumerate() {
            names.values.push(Name::new(text, (i * 3 + j) as u64, spelling));
        }
    }
    for (i, (typ, _)) in decl.ptype_params.iter().enumerate() {
        if let CoreTypeDesc::Ptyp_var(name) = arena.get_core_type(*typ).ptyp_desc {
            let text = arena.get_string(name);
            names.types.push(Name::new(text, (1 << 32) + i as u64, Spelling::Plain));
            for (j, spelling) in [Spelling::Encoder, Spelling::Decoder].into_iter().enumerate() {
                names.values.push(Name::new(text, (2 << 32) + (i * 2 + j) as u64, spelling));
            }
        }
    }
    let class = match &decl.ptype_kind {
        TypeKind::Ptype_record(labels) => { fields(&mut names, labels, arena); "record" }
        TypeKind::Ptype_variant(constructors) => {
            for (i, ctor) in constructors.iter().enumerate() {
                names.constructors.push(Name::new(arena.get_string(ctor.pcd_name.txt), i as u64, Spelling::Plain));
                if !renamed(&ctor.pcd_attributes, "spice.as", arena) { names.literals.push(Name::new(arena.get_string(ctor.pcd_name.txt), (2 << 32) + i as u64, Spelling::Plain)); }
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
        if let CoreTypeDesc::Ptyp_variant(inner) = &arena.get_core_type(manifest).ptyp_desc {
            for (i, row) in inner.0.iter().enumerate() {
                if let RowField::Rtag(label, attrs, _, _) = row {
                    names.constructors.push(Name::new(&label.txt, i as u64, Spelling::Plain));
                    if !renamed(attrs, "spice.as", arena) { names.literals.push(Name::new(&label.txt, (2 << 32) + i as u64, Spelling::Plain)); }
                }
            }
        }
    }
    names.sort();
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
    fn visitor_layout() {
        assert_eq!(std::mem::size_of::<Visitor<'_, '_>>(), 16);
        assert_eq!(std::mem::size_of::<Name<'_>>(), 32);
        assert_eq!(std::mem::size_of::<Spelling>(), 1);
    }
    #[test]
    fn virtual_names_sort_and_scan_ten_thousand_elements() {
        let stems: Vec<_> = (0..10_000).map(|i| format!("name{i:05}")).collect();
        let mut names = Names::default();
        for (i, stem) in stems.iter().enumerate().rev() {
            names.values.push(Name::new(stem, i as u64, Spelling::Encode));
        }
        let mut comparisons = 0;
        names.sort_with(|a, b| { comparisons += 1; a.bytes().cmp(b.bytes()) });
        assert!((19_998..=280_000).contains(&comparisons), "{comparisons}");
        for (i, name) in names.values.iter().enumerate() {
            assert_eq!(name.id, i as u64);
            assert!(name.bytes().eq(format!("name{i:05}_encode").bytes()));
        }
        let text = "x".repeat(10_000);
        let name = Name::new(&text, 0, Spelling::Plain);
        let mut steps = 0;
        assert!(name.bytes().inspect(|_| steps += 1).eq(text.bytes()));
        assert_eq!(steps, 10_000);
    }
    #[test]
    fn wide_syntax_walks_visit_ten_thousand_children_once() {
        let zeros = vec!["0"; 10_000].join(",");
        let vars = (0..10_000).map(|i| format!("p{i}")).collect::<Vec<_>>().join(",");
        let fields = (0..10_000).map(|i| format!("f{i}:0")).collect::<Vec<_>>().join(",");
        for (source, expected) in [
            (format!("let f = unknown({zeros})"), 10_002),
            (format!("let f = ({vars}) => 0"), 10_002),
            (format!("let f = {{{fields}}}"), 10_001),
        ] {
            let mut parser = crate::parser::Parser::new("wide.res", &source);
            let items = crate::parser::module::parse_structure(&mut parser);
            assert!(!parser.has_errors());
            let StructureItemDesc::Pstr_value((_, group)) = items[0].pstr_desc else { panic!() };
            let mut body = Body { bytes: Vec::new(), nodes: 0, complete: true };
            let names = Names::default();
            Visitor { body: &mut body, names: &names }.expr(parser.arena(), parser.arena().vb_list(group)[0].pvb_expr);
            assert_eq!(body.nodes, expected);
            assert!(body.complete);
        }
        let source = format!("let ({vars}) = unknown");
        let mut parser = crate::parser::Parser::new("pattern.res", &source);
        let items = crate::parser::module::parse_structure(&mut parser);
        assert!(!parser.has_errors());
        let StructureItemDesc::Pstr_value((_, group)) = items[0].pstr_desc else { panic!() };
        let mut body = Body { bytes: Vec::new(), nodes: 0, complete: true };
        let names = Names::default();
        Visitor { body: &mut body, names: &names }.pat(parser.arena(), parser.arena().vb_list(group)[0].pvb_pat);
        assert_eq!(body.nodes, 10_001);
        let source = format!("type t = ({})", vec!["int"; 10_000].join(","));
        let mut parser = crate::parser::Parser::new("type.res", &source);
        let items = crate::parser::module::parse_structure(&mut parser);
        assert!(!parser.has_errors());
        let StructureItemDesc::Pstr_type(inner) = &items[0].pstr_desc else { panic!() };
        let mut body = Body { bytes: Vec::new(), nodes: 0, complete: true };
        Visitor { body: &mut body, names: &names }.typ(parser.arena(), inner.1[0].ptype_manifest.unwrap());
        assert_eq!(body.nodes, 10_001);
    }
    #[test]
    fn path_encoder_visits_ten_thousand_segments_once() {
        // The borrowed recursive source representation also drops recursively;
        // give this deliberately adversarial test one sufficiently large stack.
        std::thread::Builder::new().stack_size(32 * 1024 * 1024).spawn(|| {
            let mut arena = ParseArena::default();
            let x = arena.intern_string("x");
            let mut path = Longident::Lident(x);
            for _ in 1..10_000 { path = Longident::Ldot(Box::new(path), x); }
            let mut body = Body { bytes: Vec::new(), nodes: 0, complete: true };
            Visitor { body: &mut body, names: &Names::default() }.lid(&arena, &path, &[]);
            assert_eq!(body.bytes.iter().filter(|b| **b == b'd').count(), 9_999);
            assert_eq!(body.bytes.iter().filter(|b| **b == b'i').count(), 1);
            assert_eq!(body.bytes.len(), 50_000);
        }).unwrap().join().unwrap();
    }

    #[test]
    fn declaration_preparation_borrows_ten_thousand_fields() {
        let source = format!("type t = {{{}}}", (0..10_000).map(|i| format!("f{i}:int")).collect::<Vec<_>>().join(","));
        let mut parser = crate::parser::Parser::new("fields.res", &source);
        let items = crate::parser::module::parse_structure(&mut parser);
        assert!(!parser.has_errors());
        let StructureItemDesc::Pstr_type(inner) = &items[0].pstr_desc else { panic!() };
        let TypeKind::Ptype_record(labels) = &inner.1[0].ptype_kind else { panic!() };
        let mut names = Names::default();
        fields(&mut names, labels, parser.arena());
        assert_eq!(names.fields.len(), 10_000);
        assert_eq!(names.values.len(), 10_000);
        assert_eq!(names.literals.len(), 20_000);
        for (label, name) in labels.iter().zip(&names.fields) {
            assert!(std::ptr::eq(name.text, parser.arena().get_string(label.pld_name.txt)));
        }
    }

}
