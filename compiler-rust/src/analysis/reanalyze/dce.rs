//! The dead code analysis, per file: the declarations, references and
//! annotations of one typed tree (`Dce_file_processing`, `Dead_value`,
//! `Dead_type`, `Dead_exception`, `Dead_optional_args`, `Side_effects` and
//! `Collect_annotations` in analysis/reanalyze/src).

use super::annotation;
use super::common::*;
use super::log::{Log, filename_concat, has_prefix, is_relative};
use super::traverse::{self, Visitor};
use crate::parse_arena::LocIdx;
use crate::parser::ast::{Attribute, Attributes, RecFlag};
use crate::types::decl::{self, SignatureItem};
use crate::types::type_expr::TypeDesc;
use crate::types::typedtree as tt;
use crate::types::typedtree::{TExprIdx, TPatIdx};
use crate::types::{Path as TypePath, TypeExprRef};
use indexmap::{IndexMap, IndexSet};
use std::collections::{BTreeSet, HashSet};

/// `Optional_args.t`: how the calls of a function use its optional
/// arguments.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct OptionalArgs {
    /// The number of calls seen.
    pub count: i32,
    /// The arguments no call passes.
    pub unused: BTreeSet<String>,
    /// The arguments every call passes.
    pub always_used: BTreeSet<String>,
}

impl OptionalArgs {
    /// `Optional_args.from_list`.
    pub fn from_list(names: Vec<String>) -> OptionalArgs {
        OptionalArgs {
            count: 0,
            unused: names.into_iter().collect(),
            always_used: BTreeSet::new(),
        }
    }

    /// `Optional_args.is_empty`.
    pub fn is_empty(&self) -> bool {
        self.unused.is_empty()
    }

    /// `Optional_args.apply_call`.
    pub fn apply_call(&self, arg_names: &[String], arg_names_maybe: &[String]) -> OptionalArgs {
        let maybe: BTreeSet<&String> = arg_names_maybe.iter().collect();
        let always: BTreeSet<String> = arg_names
            .iter()
            .filter(|name| !maybe.contains(name))
            .cloned()
            .collect();
        let always_used = if self.count == 0 {
            always
        } else {
            always.intersection(&self.always_used).cloned().collect()
        };
        let mut unused = self.unused.clone();
        for name in arg_names {
            unused.remove(name);
        }
        OptionalArgs {
            count: self.count + 1,
            unused,
            always_used,
        }
    }

    /// `Optional_args.combine_pair`.
    pub fn combine_pair(x: &OptionalArgs, y: &OptionalArgs) -> (OptionalArgs, OptionalArgs) {
        let unused: BTreeSet<String> = x.unused.intersection(&y.unused).cloned().collect();
        let always_used: BTreeSet<String> = x
            .always_used
            .intersection(&y.always_used)
            .cloned()
            .collect();
        (
            OptionalArgs {
                count: x.count,
                unused: unused.clone(),
                always_used: always_used.clone(),
            },
            OptionalArgs {
                count: y.count,
                unused,
                always_used,
            },
        )
    }
}

/// `Decl.Kind.t`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclKind {
    /// An exception.
    Exception,
    /// A record label.
    RecordLabel,
    /// A variant case.
    VariantCase,
    /// A value.
    Value {
        /// Whether it is bound at the top level of its module.
        is_toplevel: bool,
        /// Whether its optional arguments are reported on.
        reports_optional_args: bool,
        /// Its optional arguments.
        optional_args: OptionalArgs,
        /// Whether its definition may have side effects.
        side_effects: bool,
    },
}

impl DeclKind {
    /// `Decl.Kind.is_type`.
    pub fn is_type(&self) -> bool {
        matches!(self, DeclKind::RecordLabel | DeclKind::VariantCase)
    }

    /// `Decl.Kind.to_string`.
    fn to_str(&self) -> &'static str {
        match self {
            DeclKind::Exception => "Exception",
            DeclKind::RecordLabel => "RecordLabel",
            DeclKind::VariantCase => "VariantCase",
            DeclKind::Value { .. } => "Value",
        }
    }
}

/// `Decl.pos_adjustment`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PosAdjustment {
    /// The first case of a variant.
    FirstVariant,
    /// A later case, whose location includes its `| `.
    OtherVariant,
    /// Anything else.
    Nothing,
}

/// `Decl.t`.
#[derive(Debug, Clone)]
pub struct Decl {
    /// What is declared.
    pub decl_kind: DeclKind,
    /// The location of the module declaring it.
    pub module_loc: Loc,
    /// How the reported location differs from the declared one.
    pub pos_adjustment: PosAdjustment,
    /// The declaration's path, its own name first.
    pub path: DcePath,
    /// For a label or case of a re-exported type (`type y = x = {...}`),
    /// the path of the type it re-exports.
    pub manifest_type_path: Option<DcePath>,
    /// The position that identifies the declaration.
    pub pos: Pos,
    /// Where the declaration ends.
    pub pos_end: Pos,
    /// Where the declaration starts.
    pub pos_start: Pos,
}

impl Decl {
    /// `Decl.is_value`.
    pub fn is_value(&self) -> bool {
        matches!(self.decl_kind, DeclKind::Value { .. })
    }
}

/// `File_annotations.annotated_as`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnnotatedAs {
    /// `@genType`.
    GenType,
    /// `@dead`.
    Dead,
    /// `@live`.
    Live,
}

/// `Cross_file_items.optional_arg_call`.
#[derive(Debug, Clone)]
pub struct OptionalArgCall {
    /// The binding the call is in.
    pub pos_from: Pos,
    /// The function called.
    pub pos_to: Pos,
    /// The optional arguments the call passes.
    pub arg_names: Vec<String>,
    /// Those it passes as an option that may be `None`.
    pub arg_names_maybe: Vec<String>,
}

/// `Cross_file_items.coercion`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Coercion {
    /// The paths the coerced record's type may have.
    pub source_type_paths: Vec<DcePath>,
    /// The paths the type coerced to may have.
    pub target_type_paths: Vec<DcePath>,
}

/// `Cross_file_items.t`: what is resolved once every file is read. Each
/// list is in the order OCaml's builder holds it: the last added first.
#[derive(Debug, Clone, Default)]
pub struct CrossFileItems {
    /// Uses of exceptions other files declare: the exception's path and
    /// where it is used.
    pub exception_refs: Vec<(DcePath, Loc)>,
    /// Calls of functions with optional arguments.
    pub optional_arg_calls: Vec<OptionalArgCall>,
    /// Functions standing for each other: `(pos_from, pos_to)`.
    pub function_refs: Vec<(Pos, Pos)>,
    /// Functions with optional arguments used as values: `(pos_from,
    /// pos_to)`.
    pub optional_arg_value_escapes: Vec<(Pos, Pos)>,
    /// Record coercions.
    pub coercions: Vec<Coercion>,
}

/// `Dce_file_processing.file_data`.
#[derive(Debug, Default)]
pub struct FileData {
    /// `@dead`, `@live` and `@genType` annotations, by position.
    pub annotations: IndexMap<Pos, AnnotatedAs>,
    /// The declarations, by position.
    pub decls: IndexMap<Pos, Decl>,
    /// Value references: from a position to the declarations it uses.
    pub value_refs_from: IndexMap<Pos, IndexSet<Pos>>,
    /// Type references: from a position to the labels and cases it uses.
    pub type_refs_from: IndexMap<Pos, IndexSet<Pos>>,
    /// What is resolved once every file is read.
    pub cross_file: CrossFileItems,
}

/// `Dead_optional_args.has_optional_args`.
fn has_optional_args(tree: &Tree<'_>, mut ty: TypeExprRef) -> bool {
    loop {
        match &*tree.types.get_desc(ty) {
            TypeDesc::Tarrow { args, .. } => {
                return tree
                    .types
                    .type_args(*args)
                    .iter()
                    .any(|arg| arg.label().is_optional());
            }
            TypeDesc::Tlink(t) | TypeDesc::Tsubst(t) => ty = *t,
            _ => return false,
        }
    }
}

/// `Dead_optional_args.from_type_expr`.
fn optional_args_of_type(tree: &Tree<'_>, mut ty: TypeExprRef) -> Vec<String> {
    loop {
        match &*tree.types.get_desc(ty) {
            TypeDesc::Tarrow { args, .. } => {
                return tree
                    .types
                    .type_args(*args)
                    .iter()
                    .filter(|arg| arg.label().is_optional())
                    .filter_map(|arg| arg.label().label_name().map(str::to_string))
                    .collect();
            }
            TypeDesc::Tlink(t) | TypeDesc::Tsubst(t) => ty = *t,
            _ => return Vec::new(),
        }
    }
}

const WHITE_LIST_SIDE_EFFECTS: [&str; 8] = [
    "Pervasives./.",
    "Pervasives.ref",
    "Int64.mul",
    "Int64.neg",
    "Int64.sub",
    "Int64.shift_left",
    "Int64.one",
    "String.length",
];

/// `Side_effects.expr_no_side_effects`.
fn expr_no_side_effects(ta: &tt::TypedArena, e: TExprIdx) -> bool {
    use tt::ExpressionDesc::*;
    let all = |list: tt::TExprList| {
        ta.expr_list(list)
            .iter()
            .all(|e| expr_no_side_effects(ta, *e))
    };
    let opt = |e: &Option<TExprIdx>| e.is_none_or(|e| expr_no_side_effects(ta, e));
    let case = |c: &tt::Case| opt(&c.c_guard) && expr_no_side_effects(ta, c.c_rhs);
    match &ta.expr(e).exp_desc {
        Texp_ident(..) | Texp_constant(_) => true,
        Texp_construct(_, _, args) => all(*args),
        Texp_function { .. } => true,
        Texp_break | Texp_continue => false,
        Texp_apply { funct, args, .. } => match &ta.expr(*funct).exp_desc {
            Texp_ident(path, _, _)
                if type_path_dotted(path)
                    .is_some_and(|s| WHITE_LIST_SIDE_EFFECTS.contains(&s.as_str())) =>
            {
                ta.apply_args(*args).iter().all(|arg| opt(&arg.expression))
            }
            _ => false,
        },
        Texp_sequence(e1, e2) => expr_no_side_effects(ta, *e1) && expr_no_side_effects(ta, *e2),
        Texp_let(_, vbs, body) => {
            ta.value_bindings(*vbs)
                .iter()
                .all(|vb| expr_no_side_effects(ta, vb.vb_expr))
                && expr_no_side_effects(ta, *body)
        }
        Texp_record {
            fields,
            extended_expression,
            ..
        } => {
            ta.record_fields(*fields)
                .iter()
                .all(|(_, _, e)| expr_no_side_effects(ta, *e))
                && opt(extended_expression)
        }
        Texp_assert(_) => false,
        Texp_match(e, cases_ok, cases_exn, partial) => {
            *partial == tt::Partial::Total
                && expr_no_side_effects(ta, *e)
                && ta.cases(*cases_ok).iter().all(case)
                && ta.cases(*cases_exn).iter().all(case)
        }
        Texp_letmodule(..) => false,
        Texp_try(e, cases, finally) => {
            expr_no_side_effects(ta, *e) && ta.cases(*cases).iter().all(case) && opt(finally)
        }
        Texp_tuple(list) | Texp_array(list) => all(*list),
        Texp_variant(_, e) => opt(e),
        Texp_field(e, _, _) => expr_no_side_effects(ta, *e),
        Texp_setfield(..) => false,
        Texp_dict(entries) => ta.dict_entries(*entries).iter().all(|entry| match entry {
            tt::DictEntry::Tdict_entry(_, e) => expr_no_side_effects(ta, *e),
            tt::DictEntry::Tdict_spread(_) => false,
        }),
        Texp_spread(..) => false,
        Texp_ifthenelse(e1, e2, e3) => {
            expr_no_side_effects(ta, *e1) && expr_no_side_effects(ta, *e2) && opt(e3)
        }
        Texp_while(e1, e2) => expr_no_side_effects(ta, *e1) && expr_no_side_effects(ta, *e2),
        Texp_for(_, _, e1, e2, _, e3) => {
            expr_no_side_effects(ta, *e1)
                && expr_no_side_effects(ta, *e2)
                && expr_no_side_effects(ta, *e3)
        }
        Texp_template { values, .. } => all(*values),
        Texp_for_of(..) | Texp_for_await_of(..) | Texp_tagged_template { .. } => false,
        Texp_object_literal(fields) => fields.iter().all(|(_, e)| expr_no_side_effects(ta, *e)),
        Texp_object_get(..) | Texp_object_set(..) => false,
        Texp_letexception(_, e) => expr_no_side_effects(ta, *e),
        Texp_pack(_) => false,
    }
}

/// `Side_effects.check_expr`.
fn has_side_effects(ta: &tt::TypedArena, e: TExprIdx) -> bool {
    !expr_no_side_effects(ta, e)
}

/// The typed tree of a file.
#[derive(Clone, Copy)]
pub enum Annots<'t> {
    /// An implementation.
    Implementation(&'t tt::Structure),
    /// An interface.
    Interface(&'t tt::TypedSignature),
}

/// What the attributes of an item say about it.
#[derive(Default, Clone, Copy)]
struct AttributeFacts {
    gentype: bool,
    dead: bool,
    live: bool,
    suppress_dead_warning: bool,
}

impl AttributeFacts {
    fn of_parsed<'a>(
        arena: &crate::parse_arena::ParseArena,
        attributes: impl IntoIterator<Item = &'a Attribute> + Clone,
    ) -> AttributeFacts {
        let has = |check: &dyn Fn(&str) -> bool| {
            annotation::get_attribute_payload(arena, check, attributes.clone()).is_some()
        };
        AttributeFacts {
            gentype: has(&annotation::tag_is_one_of_the_gentype_annotations),
            dead: has(&|s| s == "dead"),
            live: has(&|s| s == "live"),
            suppress_dead_warning: annotation::is_ocaml_suppress_dead_warning(
                arena,
                attributes.clone(),
            ),
        }
    }

    /// The facts of attributes copied from another declaration (a record
    /// spread's labels), kept in their portable form.
    fn of_decl(attributes: &[decl::Attribute]) -> AttributeFacts {
        let find =
            |check: &dyn Fn(&str) -> bool| attributes.iter().find(|a| check(&a.attr_name.txt));
        AttributeFacts {
            gentype: find(&annotation::tag_is_one_of_the_gentype_annotations).is_some(),
            dead: find(&|s| s == "dead").is_some(),
            live: find(&|s| s == "live").is_some(),
            suppress_dead_warning: find(&|s| s == "warning").is_some_and(|a| {
                matches!(a.attr_payload.semantic_string(), Ok(Some(s))
                    if s.contains("-32") || s.contains("-unused-value-declaration"))
            }),
        }
    }

    fn or(self, other: AttributeFacts) -> AttributeFacts {
        AttributeFacts {
            gentype: self.gentype || other.gentype,
            dead: self.dead || other.dead,
            live: self.live || other.live,
            suppress_dead_warning: self.suppress_dead_warning || other.suppress_dead_warning,
        }
    }
}

/// `Collect_annotations.collect_export_locations`.
struct AnnotationCollector<'t, 'c> {
    tree: &'t Tree<'t>,
    config: &'c Config,
    annotations: IndexMap<Pos, AnnotatedAs>,
    do_gentype: bool,
    currently_disable_warnings: bool,
    current_scope_default: Option<AnnotatedAs>,
}

impl<'t> AnnotationCollector<'t, '_> {
    /// `Collect_annotations.process_attributes`.
    fn process_attributes(
        &mut self,
        do_gentype: bool,
        name: &str,
        pos: Pos,
        facts: AttributeFacts,
    ) {
        if let Some(default) = self.current_scope_default {
            self.annotations.insert(pos, default);
        }
        if do_gentype && facts.gentype {
            self.annotations.insert(pos, AnnotatedAs::GenType);
        }
        if facts.dead {
            self.annotations.insert(pos, AnnotatedAs::Dead);
        }
        if facts.live || self.name_is_in_live_names_or_paths(name, pos) {
            self.annotations.insert(pos, AnnotatedAs::Live);
        }
        if facts.suppress_dead_warning {
            self.annotations.insert(pos, AnnotatedAs::Live);
        }
    }

    fn name_is_in_live_names_or_paths(&self, name: &str, pos: Pos) -> bool {
        let cli = &self.config.cli;
        if cli.live_names.iter().any(|n| n == name) {
            return true;
        }
        if cli.live_paths.is_empty() {
            return false;
        }
        let fname = self.tree.files.name(pos.file);
        // collect_annotations.ml:34-38 joins the working directory to an
        // absolute name, not to a relative one.
        let fname = if is_relative(&fname) {
            fname.to_string()
        } else {
            filename_concat(&self.config.cwd, &fname)
        };
        cli.live_paths
            .iter()
            .any(|prefix| has_prefix(&fname, prefix))
    }

    fn parsed(&self, attributes: &Attributes) -> AttributeFacts {
        AttributeFacts::of_parsed(self.tree.arena, attributes.iter())
    }

    fn label(&self, ld: &tt::TypedLabelDeclaration) -> AttributeFacts {
        match &ld.ld_types_attributes {
            Some(attributes) => AttributeFacts::of_decl(attributes),
            None => self.parsed(&ld.ld_attributes),
        }
    }

    /// The scope default a top-level attribute sets
    /// (`scope_default_from_toplevel_attribute`), or that it disables the
    /// unused value warning.
    fn toplevel_attribute(&mut self, attribute: &Attribute) {
        let facts = AttributeFacts::of_parsed(self.tree.arena, std::iter::once(attribute));
        let has_gentype = annotation::get_attribute_payload(
            self.tree.arena,
            |s| s == "genType",
            std::iter::once(attribute),
        )
        .is_some();
        if facts.dead {
            self.current_scope_default = Some(AnnotatedAs::Dead);
        } else if facts.live {
            self.current_scope_default = Some(AnnotatedAs::Live);
        } else if has_gentype {
            self.current_scope_default = Some(AnnotatedAs::GenType);
        } else if facts.suppress_dead_warning {
            self.currently_disable_warnings = true;
        }
    }
}

impl<'t> Visitor<'t> for AnnotationCollector<'t, '_> {
    fn ta(&self) -> &'t tt::TypedArena {
        self.tree.ta
    }

    fn value_binding(&mut self, vb: &'t tt::ValueBinding) {
        let ta = self.tree.ta;
        let bound = match &ta.pattern(vb.vb_pat).pat_desc {
            tt::PatternDesc::Tpat_var(id, name) => Some((id, name)),
            tt::PatternDesc::Tpat_alias(inner, id, name)
                if matches!(ta.pattern(*inner).pat_desc, tt::PatternDesc::Tpat_any) =>
            {
                Some((id, name))
            }
            _ => None,
        };
        if let Some((id, name)) = bound {
            let pos = self.tree.loc(name.loc).start;
            if self.currently_disable_warnings {
                self.annotations.insert(pos, AnnotatedAs::Live);
            }
            let facts = self.parsed(&vb.vb_attributes);
            self.process_attributes(self.do_gentype, id.name(), pos, facts);
        }
        traverse::super_value_binding(self, vb);
    }

    fn type_declaration(&mut self, td: &'t tt::TypedTypeDeclaration) {
        let toplevel = self.parsed(&td.typ_attributes);
        match &td.typ_kind {
            tt::TypedTypeKind::Ttype_record(labels) => {
                for ld in labels {
                    let facts = toplevel.or(self.label(ld));
                    let pos = self.tree.loc(ld.ld_loc).start;
                    self.process_attributes(false, "", pos, facts);
                }
            }
            tt::TypedTypeKind::Ttype_variant(constructors) => {
                for cd in constructors {
                    let constructor = toplevel.or(self.parsed(&cd.cd_attributes));
                    if let tt::TypedConstructorArguments::Cstr_record(labels) = &cd.cd_args {
                        for ld in labels {
                            let facts = constructor.or(self.label(ld));
                            let pos = self.tree.loc(ld.ld_loc).start;
                            self.process_attributes(false, "", pos, facts);
                        }
                    }
                    let pos = self.tree.loc(cd.cd_loc).start;
                    self.process_attributes(false, "", pos, constructor);
                }
            }
            tt::TypedTypeKind::Ttype_abstract | tt::TypedTypeKind::Ttype_open => {}
        }
    }

    fn value_description(&mut self, vd: &'t tt::TypedValueDescription, item_loc: LocIdx) {
        let pos = self.tree.loc(item_loc).start;
        if self.currently_disable_warnings {
            self.annotations.insert(pos, AnnotatedAs::Live);
        }
        let facts = self.parsed(&vd.val_attributes);
        self.process_attributes(self.do_gentype, vd.val_id.name(), pos, facts);
    }

    fn structure_item(&mut self, item: &'t tt::StructureItem) {
        if let tt::StructureItemDesc::Tstr_attribute(attribute) = &item.str_desc {
            self.toplevel_attribute(attribute);
        }
        traverse::super_structure_item(self, item);
    }

    fn structure(&mut self, s: &'t tt::Structure) {
        let old = (self.currently_disable_warnings, self.current_scope_default);
        traverse::super_structure(self, s);
        (self.currently_disable_warnings, self.current_scope_default) = old;
    }

    fn signature_item(&mut self, item: &'t tt::TypedSignatureItem) {
        if let tt::TypedSignatureItemDesc::Tsig_attribute(attribute) = &item.sig_desc {
            self.toplevel_attribute(attribute);
        }
        traverse::super_signature_item(self, item);
    }

    fn signature(&mut self, s: &'t tt::TypedSignature) {
        let old = (self.currently_disable_warnings, self.current_scope_default);
        traverse::super_signature(self, s);
        (self.currently_disable_warnings, self.current_scope_default) = old;
    }
}

/// The declarations and references of a file (`Dead_value`).
struct Collector<'t, 'l, 'c> {
    tree: &'t Tree<'t>,
    log: &'l mut Log<'c>,
    debug: bool,
    analyze_externals: bool,
    file: &'t FileContext,
    data: FileData,
    /// The callees of direct calls: an identifier in this set is called, any
    /// other use of a function lets it escape.
    direct_callees: HashSet<TExprIdx>,
    last_binding: Loc,
    module_path: ModulePath,
}

impl<'t> Collector<'t, '_, '_> {
    /// `module_path.path @ [File_context.module_name_tagged file]`.
    fn module_context(&self, module_path: &ModulePath) -> DcePath {
        let mut path = module_path.path.clone();
        path.push(self.file.module_name_tagged());
        path
    }

    /// `Dead_common.add_value_reference`.
    fn add_value_reference(&mut self, binding: Loc, loc_from: Loc, loc_to: Loc) {
        let effective_from = if binding.is_none() { loc_from } else { binding };
        if !effective_from.ghost {
            if self.debug {
                let line = format!(
                    "add_value_reference {} --> {}\n",
                    self.log.pos_string(&effective_from.start),
                    self.log.pos_string(&loc_to.start)
                );
                self.log.item(&line);
            }
            self.data
                .value_refs_from
                .entry(effective_from.start)
                .or_default()
                .insert(loc_to.start);
        }
    }

    /// `Dead_type.add_type_reference`.
    fn add_type_reference(&mut self, pos_from: Pos, pos_to: Pos) {
        if self.debug {
            let line = format!(
                "add_type_reference {} --> {}\n",
                self.log.pos_string(&pos_from),
                self.log.pos_string(&pos_to)
            );
            self.log.item(&line);
        }
        self.data
            .type_refs_from
            .entry(pos_from)
            .or_default()
            .insert(pos_to);
    }

    /// `Dead_common.addDeclaration_`.
    #[allow(clippy::too_many_arguments)]
    fn add_declaration(
        &mut self,
        pos_end: Option<Pos>,
        pos_start: Option<Pos>,
        decl_kind: DeclKind,
        path: &DcePath,
        loc: Loc,
        pos_adjustment: PosAdjustment,
        manifest_type_path: Option<DcePath>,
        module_loc: Loc,
        name: Name,
    ) {
        let pos = loc.start;
        // A signature can hold locations of other files: `module M: Set.S
        // with type elt = int` has values located in the file of `Set`.
        if loc.ghost || pos.file != self.file.source_file {
            return;
        }
        if self.debug {
            let line = format!(
                "addDeclaration_ {} {} {} path:{}\n",
                decl_kind.to_str(),
                name,
                self.log.pos_string(&pos),
                path_to_string(path)
            );
            self.log.item(&line);
        }
        let mut decl_path = Vec::with_capacity(path.len() + 1);
        decl_path.push(name);
        decl_path.extend(path.iter().cloned());
        self.data.decls.insert(
            pos,
            Decl {
                decl_kind,
                module_loc,
                pos_adjustment,
                path: decl_path,
                manifest_type_path,
                pos,
                pos_end: pos_end.unwrap_or(loc.end),
                pos_start: pos_start.unwrap_or(pos),
            },
        );
    }

    /// `Dead_common.add_value_declaration`.
    #[allow(clippy::too_many_arguments)]
    fn add_value_declaration(
        &mut self,
        is_toplevel: bool,
        reports_optional_args: bool,
        loc: Loc,
        module_loc: Loc,
        optional_args: OptionalArgs,
        path: &DcePath,
        side_effects: bool,
        name: Name,
    ) {
        self.add_declaration(
            None,
            None,
            DeclKind::Value {
                is_toplevel,
                reports_optional_args,
                optional_args,
                side_effects,
            },
            path,
            loc,
            PosAdjustment::Nothing,
            None,
            module_loc,
            name,
        );
    }

    /// `Dead_type.add_declaration`: the labels and cases of a type.
    fn add_type_declaration(
        &mut self,
        module_path: &ModulePath,
        type_name: &str,
        type_kind: &decl::TypeKind,
        manifest_type_path: Option<DcePath>,
    ) {
        let mut path_to_type = vec![name_create(type_name, true)];
        path_to_type.extend(self.module_context(module_path));
        let module_loc = module_path.loc;
        match type_kind {
            decl::TypeKind::TypeRecord(labels, _) => {
                for ld in labels.iter() {
                    let loc = self.tree.decl_loc(ld.ld_loc);
                    self.add_declaration(
                        None,
                        None,
                        DeclKind::RecordLabel,
                        &path_to_type,
                        loc,
                        PosAdjustment::Nothing,
                        manifest_type_path.clone(),
                        module_loc,
                        name_create(ld.ld_id.name(), true),
                    );
                }
            }
            decl::TypeKind::TypeVariant(constructors, _) => {
                for (i, cd) in constructors.iter().enumerate() {
                    if let decl::ConstructorArguments::CstrRecord(labels) = &cd.cd_args {
                        for ld in labels.iter() {
                            let loc = self.tree.decl_loc(ld.ld_loc);
                            let name = format!("{}.{}", cd.cd_id.name(), ld.ld_id.name());
                            self.add_declaration(
                                None,
                                None,
                                DeclKind::RecordLabel,
                                &path_to_type,
                                loc,
                                PosAdjustment::Nothing,
                                manifest_type_path.clone(),
                                module_loc,
                                name_create(&name, true),
                            );
                        }
                    }
                    let loc = self.tree.decl_loc(cd.cd_loc);
                    // A ReScript case's location can include its `| `.
                    let fname = self.tree.files.name(loc.start.file);
                    let pos_adjustment = if fname.ends_with(".res") || fname.ends_with(".resi") {
                        if i == 0 {
                            PosAdjustment::FirstVariant
                        } else {
                            PosAdjustment::OtherVariant
                        }
                    } else {
                        PosAdjustment::Nothing
                    };
                    self.add_declaration(
                        None,
                        None,
                        DeclKind::VariantCase,
                        &path_to_type,
                        loc,
                        pos_adjustment,
                        manifest_type_path.clone(),
                        module_loc,
                        name_create(cd.cd_id.name(), true),
                    );
                }
            }
            decl::TypeKind::TypeAbstract | decl::TypeKind::TypeOpen => {}
        }
    }

    /// The manifest type path of a re-exported type (`type y = x = {...}`),
    /// from the path of its manifest.
    fn manifest_type_path(&self, module_path: &ModulePath, path: &TypePath) -> DcePath {
        let p = path_from_type_path(path);
        if let [type_name] = p.as_slice() {
            let mut full = vec![type_name.clone()];
            full.extend(self.module_context(module_path));
            full
        } else if self.file.is_interface {
            path_module_to_interface(&p)
        } else {
            path_module_to_implementation(&p)
        }
    }

    /// `Dead_value.process_signature_item`.
    #[allow(clippy::too_many_arguments)]
    fn process_signature_item(
        &mut self,
        do_types: bool,
        do_values: bool,
        module_loc: Loc,
        module_path: &ModulePath,
        path: &DcePath,
        si: &SignatureItem,
    ) {
        match si {
            SignatureItem::SigType(id, t, _) if do_types => {
                let manifest_type_path = t.type_manifest.and_then(|manifest| {
                    let manifest = self.tree.types.repr(manifest);
                    match &*self.tree.types.get_desc(manifest) {
                        TypeDesc::Tconstr { path, .. } => {
                            Some(self.manifest_type_path(module_path, path))
                        }
                        _ => None,
                    }
                });
                self.add_type_declaration(module_path, id.name(), &t.type_kind, manifest_type_path);
            }
            SignatureItem::SigValue(id, vd) if do_values => {
                let loc = self.tree.decl_loc(vd.val_loc);
                if !loc.ghost {
                    let is_primitive = matches!(vd.val_kind, decl::ValueKind::ValPrim(_));
                    if !is_primitive || self.analyze_externals {
                        let optional_args =
                            OptionalArgs::from_list(optional_args_of_type(self.tree, vd.val_type));
                        let reports_optional_args = !optional_args.is_empty();
                        self.add_value_declaration(
                            true,
                            reports_optional_args,
                            loc,
                            module_loc,
                            optional_args,
                            path,
                            false,
                            name_create(id.name(), false),
                        );
                    }
                }
            }
            SignatureItem::SigModule(id, md, _) => {
                let module_loc = self.tree.decl_loc(md.md_loc);
                let name = name_create(id.name(), true);
                let inner = module_path.enter_module(name.clone(), module_loc);
                let mut inner_path = vec![name];
                inner_path.extend(path.iter().cloned());
                for item in signature_of(&md.md_type) {
                    self.process_signature_item(
                        do_types,
                        do_values,
                        module_loc,
                        &inner,
                        &inner_path,
                        item,
                    );
                }
            }
            // A module type's items are not collected.
            _ => {}
        }
    }

    /// `Dead_value.check_any_value_binding_with_no_side_effects`.
    fn check_any_value_binding_with_no_side_effects(&mut self, vb: &tt::ValueBinding) {
        let ta = self.tree.ta;
        if !matches!(ta.pattern(vb.vb_pat).pat_desc, tt::PatternDesc::Tpat_any) {
            return;
        }
        let loc = self.tree.loc(vb.vb_loc);
        if has_side_effects(ta, vb.vb_expr) || loc.ghost {
            return;
        }
        let module_path = self.module_path.clone();
        let path = self.module_context(&module_path);
        self.add_value_declaration(
            true,
            false,
            loc,
            module_path.loc,
            OptionalArgs::default(),
            &path,
            false,
            name_create("_", false),
        );
    }

    /// `Dead_value.collect_value_binding`: declare what the binding binds
    /// and return the binding its expression is in.
    fn collect_value_binding(&mut self, vb: &tt::ValueBinding) -> Loc {
        let ta = self.tree.ta;
        let old_last_binding = self.last_binding;
        self.check_any_value_binding_with_no_side_effects(vb);
        let bound = match &ta.pattern(vb.vb_pat).pat_desc {
            tt::PatternDesc::Tpat_var(id, name) => Some((id, name)),
            tt::PatternDesc::Tpat_alias(inner, id, name)
                if matches!(ta.pattern(*inner).pat_desc, tt::PatternDesc::Tpat_any) =>
            {
                Some((id, name))
            }
            _ => None,
        };
        let Some((id, name)) = bound else {
            return self.last_binding;
        };
        let loc = self.tree.loc(name.loc);
        let vb_loc = self.tree.loc(vb.vb_loc);
        if loc.ghost || vb_loc.ghost {
            return self.last_binding;
        }
        let expr = ta.expr(vb.vb_expr);
        let optional_args =
            OptionalArgs::from_list(optional_args_of_type(self.tree, expr.exp_type));
        let reports_optional_args =
            matches!(expr.exp_desc, tt::ExpressionDesc::Texp_function { .. });
        let exists = match self.data.decls.get_mut(&loc.start) {
            Some(Decl {
                decl_kind:
                    DeclKind::Value {
                        reports_optional_args: reports,
                        optional_args: args,
                        ..
                    },
                ..
            }) => {
                *reports = reports_optional_args;
                *args = optional_args.clone();
                true
            }
            _ => false,
        };
        let module_path = self.module_path.clone();
        let path = self.module_context(&module_path);
        // dead_value.ml:65-69 reads the type's descriptor without
        // following links.
        let is_first_class_module = matches!(
            &*self.tree.types.get_desc(expr.exp_type),
            TypeDesc::Tpackage { .. }
        );
        if !exists && !is_first_class_module {
            let is_toplevel = old_last_binding.is_none();
            let side_effects = has_side_effects(ta, vb.vb_expr);
            self.add_value_declaration(
                is_toplevel,
                reports_optional_args,
                loc,
                module_path.loc,
                optional_args,
                &path,
                side_effects,
                name_create(id.name(), false),
            );
        }
        if let Some(decl) = self.data.decls.get_mut(&loc.start) {
            // The binding has the location of the whole declaration; the
            // signature only had the identifier's.
            if let DeclKind::Value { side_effects, .. } = &mut decl.decl_kind {
                *side_effects = has_side_effects(ta, vb.vb_expr);
            }
            decl.pos_end = vb_loc.end;
            decl.pos_start = vb_loc.start;
        }
        loc
    }

    /// `Dead_value.process_optional_args` and
    /// `Dead_optional_args.add_references`.
    fn process_optional_args(
        &mut self,
        exp_type: TypeExprRef,
        loc_from: Loc,
        loc_to: Loc,
        path: &TypePath,
        args: &[tt::ApplyArg],
    ) {
        if !has_optional_args(self.tree, exp_type) {
            return;
        }
        let ta = self.tree.ta;
        let mut supplied = Vec::new();
        let mut supplied_maybe = Vec::new();
        for arg in args {
            let arg_is_supplied = match arg.expression {
                Some(e) => match &ta.expr(e).exp_desc {
                    tt::ExpressionDesc::Texp_construct(_, cstr, _) if cstr.cstr_name == "Some" => {
                        Some(true)
                    }
                    tt::ExpressionDesc::Texp_construct(_, cstr, _) if cstr.cstr_name == "None" => {
                        Some(false)
                    }
                    _ => None,
                },
                None => Some(false),
            };
            if let crate::types::asttypes::ArgLabel::Optional(label) = &arg.label
                && !loc_from.ghost
            {
                if arg_is_supplied != Some(false) {
                    supplied.push(label.txt.clone());
                }
                if arg_is_supplied.is_none() {
                    supplied_maybe.push(label.txt.clone());
                }
            }
        }
        // OCaml conses each name onto its list.
        supplied.reverse();
        supplied_maybe.reverse();
        let binding = self.last_binding;
        if self.debug {
            let line = format!(
                "DeadOptionalArgs.addReferences {} called with optional argNames:{} argNamesMaybe:{} {}\n",
                path_to_string(&path_from_type_path(path)),
                supplied.join(", "),
                supplied_maybe.join(", "),
                self.log.pos_string(&loc_from.start)
            );
            self.data
                .cross_file
                .optional_arg_calls
                .push(OptionalArgCall {
                    pos_from: binding.start,
                    pos_to: loc_to.start,
                    arg_names: supplied,
                    arg_names_maybe: supplied_maybe,
                });
            self.log.item(&line);
        } else {
            self.data
                .cross_file
                .optional_arg_calls
                .push(OptionalArgCall {
                    pos_from: binding.start,
                    pos_to: loc_to.start,
                    arg_names: supplied,
                    arg_names_maybe: supplied_maybe,
                });
        }
    }

    /// `Dead_value.type_path_candidates`: the paths a type may be declared
    /// under, since whether its module is an interface is not known here.
    fn type_path_candidates(&self, path: &TypePath) -> Vec<DcePath> {
        let path = path_from_type_path(path);
        let mut qualified = path.clone();
        qualified.extend(self.module_context(&self.module_path));
        let mut paths: Vec<DcePath> = Vec::new();
        for path in [path, qualified] {
            for candidate in [
                path.clone(),
                path_module_to_implementation(&path),
                path_module_to_interface(&path),
            ] {
                if !paths.contains(&candidate) {
                    // `add_unique` conses.
                    paths.insert(0, candidate);
                }
            }
        }
        paths
    }

    /// `Dead_value.add_coercion`.
    fn add_coercion(&mut self, source: TypeExprRef, target: TypeExprRef) {
        let type_paths = |this: &Self, ty: TypeExprRef| {
            let ty = this.tree.types.repr(ty);
            match &*this.tree.types.get_desc(ty) {
                TypeDesc::Tconstr { path, .. } => this.type_path_candidates(path),
                _ => Vec::new(),
            }
        };
        let source_type_paths = type_paths(self, source);
        let target_type_paths = type_paths(self, target);
        if source_type_paths.is_empty() || target_type_paths.is_empty() {
            return;
        }
        self.data.cross_file.coercions.push(Coercion {
            source_type_paths,
            target_type_paths,
        });
    }

    /// `Dead_exception.mark_as_used`.
    fn mark_exception_as_used(&mut self, loc_from: Loc, loc_to: Loc, path: &TypePath) {
        if loc_to.ghost {
            // Probably declared in another file: resolved once every file
            // is read.
            let exception_path = path_module_to_implementation(&path_from_type_path(path));
            self.data
                .cross_file
                .exception_refs
                .push((exception_path, loc_from));
        } else {
            self.add_value_reference(self.last_binding, loc_from, loc_to);
        }
    }

    /// `Dead_value.collect_expr`, before the expression's children are
    /// visited. `loc_from` is the expression's location; a record's punned
    /// field is read at its location without the ghost flag, as a copy that
    /// is no callee (`is_copy`).
    fn collect_expr(&mut self, e: TExprIdx, loc_from: Loc, is_copy: bool) {
        use tt::ExpressionDesc::*;
        let ta = self.tree.ta;
        let expr = ta.expr(e);
        let binding = self.last_binding;
        for (extra, _, _) in ta.exp_extra(expr) {
            if let tt::ExpExtra::Texp_coerce {
                source_type,
                target_type,
                ..
            } = extra
            {
                self.add_coercion(*source_type, *target_type);
            }
        }
        match &expr.exp_desc {
            Texp_ident(path, _, vd) => {
                let loc_to = self.tree.decl_loc(vd.val_loc);
                if loc_to.ghost {
                    return;
                }
                if loc_from == loc_to && path.name() == "emptyArray" {
                    // Lowercase JSX without children makes an `emptyArray`
                    // that is used at its own location.
                    if self.debug {
                        let line = format!(
                            "add_value_ref (dummy) {} --> {}\n",
                            self.log.pos_string(&Pos::NONE),
                            self.log.pos_string(&loc_to.start)
                        );
                        self.log.item(&line);
                    }
                    self.data
                        .value_refs_from
                        .entry(Pos::NONE)
                        .or_default()
                        .insert(loc_to.start);
                } else {
                    self.add_value_reference(binding, loc_from, loc_to);
                    if (is_copy || !self.direct_callees.contains(&e))
                        && has_optional_args(self.tree, vd.val_type)
                    {
                        // `Location.none` is a top-level expression, which
                        // runs unconditionally: use its own position.
                        let pos_from = if binding.is_none() {
                            loc_from.start
                        } else {
                            binding.start
                        };
                        self.data
                            .cross_file
                            .optional_arg_value_escapes
                            .push((pos_from, loc_to.start));
                    }
                }
            }
            Texp_apply { funct, args, .. } => {
                let callee = ta.expr(*funct);
                if let Texp_ident(path, _, vd) = &callee.exp_desc {
                    let loc_to = self.tree.decl_loc(vd.val_loc);
                    if !loc_to.ghost {
                        self.direct_callees.insert(*funct);
                        self.process_optional_args(
                            callee.exp_type,
                            loc_from,
                            loc_to,
                            path,
                            ta.apply_args(*args),
                        );
                    }
                }
            }
            // What the checker makes of a call that omits optional
            // arguments: `let arg = f in eta => arg(eta)`.
            Texp_let(RecFlag::Nonrecursive, vbs, body) => {
                let [vb] = ta.value_bindings(*vbs) else {
                    return;
                };
                let tt::PatternDesc::Tpat_var(id_arg, _) = &ta.pattern(vb.vb_pat).pat_desc else {
                    return;
                };
                let callee = ta.expr(vb.vb_expr);
                let Texp_ident(path, _, vd) = &callee.exp_desc else {
                    return;
                };
                let Texp_function { params, body, .. } = &ta.expr(*body).exp_desc else {
                    return;
                };
                let [param] = ta.function_params(*params) else {
                    return;
                };
                let tt::PatternDesc::Tpat_var(eta_arg, _) = &ta.pattern(param.fp_pat).pat_desc
                else {
                    return;
                };
                let Texp_apply { funct, args, .. } = &ta.expr(*body).exp_desc else {
                    return;
                };
                let Texp_ident(id_arg2, _, _) = &ta.expr(*funct).exp_desc else {
                    return;
                };
                let loc_to = self.tree.decl_loc(vd.val_loc);
                if loc_to.ghost
                    || id_arg.name() != "arg"
                    || eta_arg.name() != "eta"
                    || id_arg2.name() != "arg"
                {
                    return;
                }
                self.direct_callees.insert(vb.vb_expr);
                self.process_optional_args(
                    callee.exp_type,
                    loc_from,
                    loc_to,
                    path,
                    ta.apply_args(*args),
                );
            }
            Texp_field(_, _, label) => {
                let loc_to = self.tree.decl_loc(label.lbl_loc);
                if !loc_to.ghost {
                    self.add_type_reference(loc_from.start, loc_to.start);
                }
            }
            Texp_construct(_, cstr, _) => {
                let loc_to = self.tree.decl_loc(cstr.cstr_loc);
                if let decl::ConstructorKind::Extension(path) = &cstr.cstr_kind {
                    self.mark_exception_as_used(loc_from, loc_to, path);
                }
                if !loc_to.ghost {
                    self.add_type_reference(loc_from.start, loc_to.start);
                }
            }
            Texp_record { fields, .. } => {
                for (_, _, field) in ta.record_fields(*fields) {
                    let loc = self.tree.loc(ta.expr(*field).exp_loc);
                    if loc.ghost {
                        // A punned field of an OCaml project has a ghost
                        // location.
                        self.collect_expr(
                            *field,
                            Loc {
                                ghost: false,
                                ..loc
                            },
                            true,
                        );
                        traverse::super_expr(self, *field);
                    }
                }
            }
            _ => {}
        }
    }

    /// `Dead_value.add_record_rest_type_references`: a record pattern's rest
    /// reads every label of the rest's type.
    fn add_record_rest_type_references(&mut self, pat: &tt::Pattern, rest: &tt::RecordPatternRest) {
        let pos_from = self.tree.loc(rest.rest_name.loc).start;
        let types = self.tree.types;
        let concrete = types.get_typed_env(pat.pat_env).and_then(|env| {
            crate::types::ctype::extract_concrete_typedecl(types, &env, rest.rest_type)
        });
        if let Some((_, _, decl)) = &concrete
            && let decl::TypeKind::TypeRecord(labels, _) = &decl.type_kind
        {
            for ld in labels.iter() {
                let loc = self.tree.decl_loc(ld.ld_loc);
                if !loc.ghost {
                    self.add_type_reference(pos_from, loc.start);
                }
            }
            return;
        }
        // `add_record_rest_type_references_from_path`.
        let rest_type = types.repr(rest.rest_type);
        let TypeDesc::Tconstr { path, .. } = &*types.get_desc(rest_type) else {
            return;
        };
        let type_paths = self.type_path_candidates(path);
        let labels: Vec<Pos> = self
            .data
            .decls
            .values()
            .filter(|decl| {
                decl.decl_kind == DeclKind::RecordLabel
                    && type_paths
                        .iter()
                        .any(|candidate| candidate[..] == decl.path[1..])
            })
            .map(|decl| decl.pos)
            .collect();
        for pos_to in labels {
            self.add_type_reference(pos_from, pos_to);
        }
    }

    /// `Dead_value.process_value_dependency`: a value an interface or a
    /// signature exports uses the value implementing it.
    fn process_value_dependency(
        &mut self,
        value: &decl::ValueDescription,
        spec: &decl::ValueDescription,
    ) {
        let loc_to = self.tree.decl_loc(value.val_loc);
        let loc_from = self.tree.decl_loc(spec.val_loc);
        if loc_to.ghost || loc_from.ghost || loc_to.start == loc_from.start {
            return;
        }
        self.add_value_reference(Loc::NONE, loc_from, loc_to);
        if has_optional_args(self.tree, value.val_type)
            && has_optional_args(self.tree, spec.val_type)
        {
            // `Dead_optional_args.add_function_reference`.
            if self.debug {
                let line = format!(
                    "Dead_optional_args.add_function_reference {} {}\n",
                    self.log.pos_string(&loc_from.start),
                    self.log.pos_string(&loc_to.start)
                );
                self.log.item(&line);
            }
            self.data
                .cross_file
                .function_refs
                .push((loc_from.start, loc_to.start));
        }
    }
}

/// `Dead_value.get_signature`.
fn signature_of(module_type: &decl::ModuleType) -> &[SignatureItem] {
    match module_type {
        decl::ModuleType::MtySignature(signature) => signature,
        decl::ModuleType::MtyFunctor { result, .. } => signature_of(result),
        decl::ModuleType::MtyIdent(_) | decl::ModuleType::MtyAlias(..) => &[],
    }
}

impl<'t> Visitor<'t> for Collector<'t, '_, '_> {
    fn ta(&self) -> &'t tt::TypedArena {
        self.tree.ta
    }

    fn expr(&mut self, e: TExprIdx) {
        let loc_from = self.tree.loc(self.tree.ta.expr(e).exp_loc);
        self.collect_expr(e, loc_from, false);
        traverse::super_expr(self, e);
    }

    /// `Dead_value.collect_pattern`.
    fn pat(&mut self, p: TPatIdx) {
        let pat = self.tree.ta.pattern(p);
        if let tt::PatternDesc::Tpat_record(fields, _, rest) = &pat.pat_desc {
            let pos_from = self.tree.loc(pat.pat_loc).start;
            for (_, label, _, _) in fields {
                let pos_to = self.tree.decl_loc(label.lbl_loc).start;
                self.add_type_reference(pos_from, pos_to);
            }
            if let Some(rest) = rest {
                self.add_record_rest_type_references(pat, rest);
            }
        }
        traverse::super_pat(self, p);
    }

    fn structure_item(&mut self, item: &'t tt::StructureItem) {
        use tt::StructureItemDesc::*;
        let ta = self.tree.ta;
        let mut entered: Option<ModulePath> = None;
        match &item.str_desc {
            Tstr_module(mb) => {
                let module_expr = ta.module_expr(mb.mb_expr);
                let inner = self
                    .module_path
                    .enter_module(name_create(mb.mb_id.name(), true), self.tree.loc(mb.mb_loc));
                if matches!(
                    module_expr.mod_desc,
                    tt::ModuleExprDesc::Tmod_constraint(..)
                ) && let decl::ModuleType::MtySignature(signature) = &module_expr.mod_type
                {
                    let module_loc = self.tree.loc(module_expr.mod_loc);
                    let path = self.module_context(&inner);
                    for si in signature.iter() {
                        self.process_signature_item(true, false, module_loc, &inner, &path, si);
                    }
                }
                entered = Some(inner);
            }
            Tstr_type(_, declarations) => {
                let module_path = self.module_path.clone();
                for td in declarations {
                    let manifest_type_path = td.typ_manifest.and_then(|manifest| {
                        match &ta.core_type(manifest).ctyp_desc {
                            tt::TypedCoreTypeDesc::Ttyp_constr(path, _, _) => {
                                Some(self.manifest_type_path(&module_path, path))
                            }
                            _ => None,
                        }
                    });
                    self.add_type_declaration(
                        &module_path,
                        td.typ_id.name(),
                        &td.typ_type.type_kind,
                        manifest_type_path,
                    );
                }
            }
            Tstr_include(incl) => {
                let module_expr = ta.module_expr(incl.incl_mod);
                if matches!(module_expr.mod_desc, tt::ModuleExprDesc::Tmod_ident(..)) {
                    let module_path = self.module_path.clone();
                    let path = self.module_context(&module_path);
                    let module_loc = self.tree.loc(module_expr.mod_loc);
                    for si in &incl.incl_type {
                        self.process_signature_item(
                            true,
                            false,
                            module_loc,
                            &module_path,
                            &path,
                            si,
                        );
                    }
                }
            }
            Tstr_exception(ext) => {
                let ext = ta.extension_constructor(*ext);
                let module_path = self.module_path.clone();
                let path = self.module_context(&module_path);
                let str_loc = self.tree.loc(item.str_loc);
                // `Dead_exception.add`.
                self.add_declaration(
                    Some(str_loc.end),
                    Some(str_loc.start),
                    DeclKind::Exception,
                    &path,
                    self.tree.loc(ext.ext_loc),
                    PosAdjustment::Nothing,
                    None,
                    module_path.loc,
                    name_create(ext.ext_id.name(), true),
                );
            }
            _ => {}
        }
        match entered {
            Some(inner) => {
                let outer = std::mem::replace(&mut self.module_path, inner);
                traverse::super_structure_item(self, item);
                self.module_path = outer;
            }
            None => traverse::super_structure_item(self, item),
        }
    }

    fn value_binding(&mut self, vb: &'t tt::ValueBinding) {
        let loc = self.collect_value_binding(vb);
        let outer = std::mem::replace(&mut self.last_binding, loc);
        traverse::super_value_binding(self, vb);
        self.last_binding = outer;
    }
}

/// `Dce_file_processing.process_cmt_file`: the dead code data of a file.
/// `interface_exists` says an implementation has an interface, whose
/// `@genType` annotations then count instead of its own.
pub fn process_file<'t>(
    tree: &'t Tree<'t>,
    log: &mut Log<'_>,
    config: &Config,
    file: &'t FileContext,
    annots: Annots<'t>,
    interface_exists: bool,
) -> FileData {
    let do_gentype = match annots {
        Annots::Interface(_) => true,
        Annots::Implementation(_) => !interface_exists,
    };
    let mut annotations = AnnotationCollector {
        tree,
        config,
        annotations: IndexMap::new(),
        do_gentype,
        currently_disable_warnings: false,
        current_scope_default: None,
    };
    match annots {
        Annots::Interface(signature) => annotations.signature(signature),
        Annots::Implementation(structure) => annotations.structure(structure),
    }
    let mut collector = Collector {
        tree,
        debug: config.cli.debug,
        analyze_externals: config.cli.analyze_externals,
        log,
        file,
        data: FileData {
            annotations: annotations.annotations,
            ..FileData::default()
        },
        direct_callees: HashSet::new(),
        last_binding: Loc::NONE,
        module_path: ModulePath::initial(),
    };
    // `Dce_file_processing.process_signature`.
    let module_path = ModulePath::initial();
    let path = vec![file.module_name_tagged()];
    match annots {
        Annots::Interface(signature) => {
            let items = crate::types::typemod::decl_signature_from_typed_signature(
                tree.ta, signature, tree.arena, tree.types,
            );
            for si in items.iter() {
                collector.process_signature_item(true, true, Loc::NONE, &module_path, &path, si);
            }
        }
        Annots::Implementation(structure) => {
            for si in &structure.str_type {
                collector.process_signature_item(false, true, Loc::NONE, &module_path, &path, si);
            }
            collector.structure(structure);
            // OCaml's list has the most recent dependency first, and
            // `Dead_value.process_structure` reverses it.
            let mut dependencies = tree.types.value_dependencies();
            dependencies.reverse();
            for (value, spec) in &dependencies {
                collector.process_value_dependency(value, spec);
            }
        }
    }
    collector.data
}
