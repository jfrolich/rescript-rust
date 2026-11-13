//! Which derived items take a plan, and the plan of a constructor
//! application (`compiler-rust/docs/DERIVED_CODECS.md`, Q5 and slice 1).
//!
//! The plan describes the bindings `generate_codec_decls` makes for a type
//! whose manifest is a constructor application, such as `array<id>`:
//!
//! ```text
//! let ids_encode = v => Spice.arrayToJson(id_encodeJson)(v)
//! ```
//!
//! The body is `Function(v, Apply(codec, [Local 0]))`, where the codec of a
//! type is the `Free` codec of its constructor applied, one partial
//! application each, to the codecs of its type arguments. The obligations are
//! the free names in the order inference meets them: a constructor's codec,
//! then those of its arguments, left to right.

use super::*;
use crate::binary_ast::derive::plan::{
    Binding, BodyIdx, BodyNode, Case, CasePattern, DerivedIdx, ExprLoc, LabelUse, NO_VAR,
    Obligation, ObligationIdx, OptionalArg, Owner, Predef, Site, SkeletonIdx, SkeletonNode, Span,
    TypeSource,
};
use crate::binary_ast::derive::{Classification, GeneralReason};
use crate::parse_arena::TypeList;

mod record;

/// Whether an attribute payload is a constant: a literal, or a template
/// without interpolation. Anything else is a user expression typed among the
/// binders of the generated body.
/// Cost: O(1), one node read; no allocation.
fn payload_is_constant(attr: &Attribute, arena: &ParseArena) -> bool {
    let Payload::PStr(items) = &attr.1 else {
        return false;
    };
    let [item] = items.as_slice() else {
        return false;
    };
    let StructureItemDesc::Pstr_eval(eval) = &item.pstr_desc else {
        return false;
    };
    match &arena.get_expr(eval.0).pexp_desc {
        ExpressionDesc::Pexp_constant(_) => true,
        ExpressionDesc::Pexp_template(template) => {
            template.values.is_empty() && template.source_segments.len() == 1
        }
        _ => false,
    }
}

/// Whether one of `names` is an attribute of `attrs`, and whether such an
/// attribute has a payload that is not a constant.
/// Cost: O(attributes · names) string comparisons; no allocation.
fn find_attributes(attrs: &[Attribute], names: &[&str], arena: &ParseArena) -> (bool, bool) {
    let (mut found, mut user_expression) = (false, false);
    for attr in attrs {
        if names.contains(&arena.get_string(attr.0.txt)) {
            found = true;
            user_expression |= !payload_is_constant(attr, arena);
        }
    }
    (found, user_expression)
}

/// What a walk over the types of a declaration found.
#[derive(Default)]
struct TypeFacts {
    /// A `@spice.codec` on a type.
    custom_codec: bool,
    /// A tuple or a polymorphic variant.
    unmeasured: bool,
    /// A type whose codec is not a plain name applied to codecs: `JSON.t`,
    /// whose codec is a function literal, or a type the derive rejects.
    unplanned: bool,
}

/// Collect the facts of one type and the types under it.
/// Cost: O(type nodes), one visit each; recursion depth is the type's depth;
/// no allocation.
fn type_facts(typ_idx: CoreTypeIdx, arena: &ParseArena, facts: &mut TypeFacts) {
    let typ = arena.get_core_type(typ_idx);
    facts.custom_codec |= typ
        .ptyp_attributes
        .iter()
        .any(|attr| arena.get_string(attr.0.txt) == "spice.codec");
    match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_constr((lid, args)) => {
            facts.unplanned |= is_json_identifier(lid.txt, arena)
                || matches!(arena.get_longident(lid.txt), Longident::Lapply(_, _));
            for i in 0..args.len() {
                type_facts(arena.type_list(*args)[i], arena, facts);
            }
        }
        CoreTypeDesc::Ptyp_tuple(items) => {
            facts.unmeasured = true;
            for i in 0..items.len() {
                type_facts(arena.type_list(*items)[i], arena, facts);
            }
        }
        CoreTypeDesc::Ptyp_variant(_) => facts.unmeasured = true,
        CoreTypeDesc::Ptyp_any
        | CoreTypeDesc::Ptyp_var(_)
        | CoreTypeDesc::Ptyp_arrow(_)
        | CoreTypeDesc::Ptyp_object(_)
        | CoreTypeDesc::Ptyp_alias(_)
        | CoreTypeDesc::Ptyp_poly(_)
        | CoreTypeDesc::Ptyp_package(_)
        | CoreTypeDesc::Ptyp_extension(_) => facts.unplanned = true,
    }
}

/// The facts of every field of a record, and whether a `@spice.default` or
/// `@spice.key` holds a user expression.
/// Cost: O(fields + their type nodes and attributes); no allocation.
fn label_facts(labels: &[LabelDeclaration], arena: &ParseArena, facts: &mut TypeFacts) -> bool {
    let mut user_expression = false;
    for label in labels {
        type_facts(label.pld_type, arena, facts);
        user_expression |=
            find_attributes(&label.pld_attributes, &["spice.default", "spice.key"], arena).1;
    }
    user_expression
}

/// Whether two declarations of a group share a label or a constructor name:
/// the body resolves both by name, so the last declaration would win.
/// Cost: O(n log n) for the n labels and constructors of the group, one
/// buffer of n entries; called once per group that has two derived
/// declarations.
pub(in crate::binary_ast) fn group_shares_names(group: &[TypeDeclaration], arena: &ParseArena) -> bool {
    // (name, is a constructor, declaration)
    let mut names: Vec<(&str, bool, usize)> = Vec::new();
    for (i, decl) in group.iter().enumerate() {
        match &decl.ptype_kind {
            TypeKind::Ptype_record(labels) => {
                names.extend(labels.iter().map(|l| (arena.get_string(l.pld_name.txt), false, i)));
            }
            TypeKind::Ptype_variant(constructors) => {
                for constructor in constructors {
                    names.push((arena.get_string(constructor.pcd_name.txt), true, i));
                    if let ConstructorArguments::Pcstr_record(labels) = &constructor.pcd_args {
                        names.extend(
                            labels.iter().map(|l| (arena.get_string(l.pld_name.txt), false, i)),
                        );
                    }
                }
            }
            TypeKind::Ptype_abstract | TypeKind::Ptype_open => {}
        }
    }
    names.sort_unstable();
    names
        .windows(2)
        .any(|pair| pair[0].0 == pair[1].0 && pair[0].1 == pair[1].1 && pair[0].2 != pair[1].2)
}

/// Classify one declaration that derives codecs: the plan path, or the
/// general path with the first reason of the Q5 table that applies. Total:
/// every declaration gets one of the two.
/// Cost: O(type nodes and attributes of the declaration), one visit each;
/// no allocation.
pub(in crate::binary_ast) fn classify(
    arena: &ParseArena,
    decl: &TypeDeclaration,
    rec_flag: RecFlag,
    shares_names: bool,
) -> Classification {
    use GeneralReason::*;
    let general = Classification::General;
    if rec_flag == RecFlag::Recursive {
        return general(RecursiveGroup);
    }
    if !decl.ptype_params.is_empty() {
        return general(TypeParameters);
    }
    let has = |name: &str| {
        decl.ptype_attributes
            .iter()
            .any(|attr| arena.get_string(attr.0.txt) == name)
    };
    if has("unboxed") {
        return general(Unboxed);
    }
    let mut facts = TypeFacts::default();
    let (has_fallback, mut user_expression) =
        find_attributes(&decl.ptype_attributes, &["spice.fallback"], arena);
    if let Some(manifest) = decl.ptype_manifest {
        type_facts(manifest, arena, &mut facts);
    }
    match &decl.ptype_kind {
        TypeKind::Ptype_record(labels) => user_expression |= label_facts(labels, arena, &mut facts),
        TypeKind::Ptype_variant(constructors) => {
            for constructor in constructors {
                match &constructor.pcd_args {
                    ConstructorArguments::Pcstr_tuple(args) => {
                        for arg in args {
                            type_facts(*arg, arena, &mut facts);
                        }
                    }
                    ConstructorArguments::Pcstr_record(labels) => {
                        user_expression |= label_facts(labels, arena, &mut facts);
                    }
                }
            }
        }
        TypeKind::Ptype_abstract | TypeKind::Ptype_open => {}
    }
    if facts.custom_codec {
        return general(CustomCodec);
    }
    if user_expression {
        return general(UserExpression);
    }
    if shares_names {
        return general(SharedNames);
    }
    let manifest_is_application = decl.ptype_manifest.is_some_and(|manifest| {
        matches!(
            arena.get_core_type(manifest).ptyp_desc,
            CoreTypeDesc::Ptyp_constr(_)
        )
    });
    if facts.unmeasured
        || has("spice.serde")
        || (decl.ptype_manifest.is_some() && !manifest_is_application && !facts.unplanned)
    {
        return general(UnmeasuredShape);
    }
    // Variants are slice 3; a constant fallback and the identity codec of
    // `JSON.t` need body nodes no slice lowers yet. A record takes a plan
    // when it has a field and its keys and defaults are literal constants.
    let planned_shape = match &decl.ptype_kind {
        TypeKind::Ptype_abstract => manifest_is_application,
        TypeKind::Ptype_record(labels) => {
            decl.ptype_manifest.is_none() && record::planned(labels, arena)
        }
        TypeKind::Ptype_variant(_) | TypeKind::Ptype_open => false,
    };
    if !planned_shape || has_fallback || facts.unplanned {
        return general(NotYetPlanned);
    }
    // A declaration that could take a plan, in a tree that is not planned.
    if let Some(reason) = arena.derived_plans_off() {
        return general(reason);
    }
    Classification::Plan
}

/// A type whose codec the plan needs.
#[derive(Clone, Copy)]
enum Spec {
    /// The codec of a type.
    Type(CoreTypeIdx, EncodeContext),
    /// `Spice.optionToJson(codec)` or `Spice.optionFromJson(codec)` for the
    /// values of a dictionary of options (`codecs_generate_dict_codecs`).
    OptionOf(CoreTypeIdx),
    /// `Spice.optionToJson(codec)` or `Spice.optionalFieldFromJson(codec)`
    /// for a record field that may be absent
    /// (`records_make_omittable_codecs`).
    Omittable(CoreTypeIdx),
}

/// Where the skeleton of a codec's head finds the type it is used at.
#[derive(Clone, Copy)]
enum Slot {
    /// The codec the binding applies to its parameter: fresh variables.
    Root,
    /// An argument that is a plain name: the variable of its parameter.
    Plain(u32),
    /// An argument that is itself an application: the variables of the
    /// parameter and the result of the function that remains.
    Applied(u32, u32),
}

/// The parts of a codec: its head name and the types whose codecs it takes.
struct Parts {
    name: LidentIdx,
    name_loc: LocIdx,
    expr_loc: ExprLoc,
    args: Args,
}

/// The codec arguments of a head.
#[derive(Clone, Copy)]
enum Args {
    /// The codecs of the type arguments, in order.
    Types(TypeList),
    /// One argument.
    One(Spec),
}

impl Args {
    fn len(self) -> usize {
        match self {
            Args::Types(list) => list.len(),
            Args::One(_) => 1,
        }
    }

    fn get(self, i: usize, arena: &ParseArena) -> Spec {
        match self {
            Args::Types(list) => Spec::Type(arena.type_list(list)[i], EncodeContext::Value),
            Args::One(spec) => spec,
        }
    }
}

struct Builder<'a> {
    arena: &'a mut ParseArena,
    side: Side,
    /// Next free skeleton variable of the binding.
    vars: u32,
    /// The slots of the arguments of the heads being emitted, innermost last:
    /// one buffer for a whole item.
    slots: &'a mut Vec<Slot>,
}

impl Builder<'_> {
    fn fresh(&mut self) -> u32 {
        self.vars += 1;
        self.vars - 1
    }

    /// The number of codecs the codec of `spec` is applied to.
    /// Cost: O(1), plus O(path depth) comparisons for a one-argument type.
    fn arity(&self, spec: Spec) -> usize {
        match spec {
            Spec::OptionOf(_) | Spec::Omittable(_) => 1,
            Spec::Type(typ, _) => match &self.arena.get_core_type(typ).ptyp_desc {
                CoreTypeDesc::Ptyp_constr((_, args)) => args.len(),
                _ => unreachable!("the classifier admits constructor applications only"),
            },
        }
    }

    /// A `Spice.<name>` identifier without a location, as `expr_ident_path`
    /// makes it.
    fn library(&mut self, name: &str, args: Args) -> Parts {
        Parts {
            name: lident_path_static(self.arena, &["Spice", name]),
            name_loc: self.arena.dummy_loc(),
            expr_loc: ExprLoc::OfName,
            args,
        }
    }

    /// The head and arguments of a codec, as `codecs_generate_codecs_for`
    /// chooses them. Cost: O(path depth) comparisons, one longident.
    fn parts(&mut self, spec: Spec) -> Parts {
        let (typ, context) = match spec {
            Spec::OptionOf(inner) => {
                let name = match self.side {
                    Side::Encode => "optionToJson",
                    Side::Decode => "optionFromJson",
                };
                return self.library(name, Args::One(Spec::Type(inner, EncodeContext::Value)));
            }
            Spec::Omittable(inner) => {
                let name = match self.side {
                    Side::Encode => "optionToJson",
                    Side::Decode => "optionalFieldFromJson",
                };
                return self.library(name, Args::One(Spec::Type(inner, EncodeContext::Value)));
            }
            Spec::Type(typ, context) => (typ, context),
        };
        let CoreTypeDesc::Ptyp_constr((lid, args)) = &self.arena.get_core_type(typ).ptyp_desc
        else {
            unreachable!("the classifier admits constructor applications only")
        };
        let (lid, args) = (*lid, *args);
        if args.len() == 1 && is_dict_identifier(lid.txt, self.arena) {
            // `codecs_generate_dict_codecs`: a dictionary of options omits
            // the absent values.
            let value = self.arena.get_core_type(self.arena.type_list(args)[0]);
            return match (default_option_inner_type(value, self.arena), self.side) {
                (None, Side::Encode) => self.library("dictToJson", Args::Types(args)),
                (None, Side::Decode) => self.library("dictFromJson", Args::Types(args)),
                (Some(inner), Side::Encode) => {
                    self.library("dictOptionalToJson", Args::One(Spec::OptionOf(inner)))
                }
                (Some(inner), Side::Decode) => {
                    self.library("dictFromJson", Args::One(Spec::OptionOf(inner)))
                }
            };
        }
        if let Some(name) = library_codec(context, self.side, lid.txt, self.arena) {
            let prefix = self.arena.spice_codecs_str();
            return Parts {
                name: lident_path_spice_prefix(self.arena, prefix, name),
                name_loc: lid.loc,
                expr_loc: ExprLoc::OfName,
                args: Args::Types(args),
            };
        }
        Parts {
            name: user_codec_lid(context, self.side, lid.txt, self.arena)
                .expect("the classifier admits no functor application"),
            name_loc: self.arena.none_loc(),
            expr_loc: ExprLoc::Dummy,
            args: Args::Types(args),
        }
    }

    /// Push the skeleton of a parameter that takes the codec of `spec`, and
    /// give the slot that codec is then emitted with: a variable for a plain
    /// name, a function of one parameter for an application.
    /// Cost: O(1): one or three skeleton nodes.
    fn arg_slot(&mut self, spec: Spec) -> Slot {
        if self.arity(spec) == 0 {
            let var = self.fresh();
            self.arena.plans_mut().push_skeleton(SkeletonNode::Var(var));
            Slot::Plain(var)
        } else {
            let (param, result) = (self.fresh(), self.fresh());
            let plans = self.arena.plans_mut();
            plans.push_skeleton(SkeletonNode::Arrow { params: 1 });
            plans.push_skeleton(SkeletonNode::Var(param));
            plans.push_skeleton(SkeletonNode::Var(result));
            Slot::Applied(param, result)
        }
    }

    /// Emit the codec of `spec`: its obligation and skeleton, then those of
    /// its arguments, and the body node that applies the head to each
    /// argument's codec in turn.
    /// Cost: O(codecs under `spec`): per codec one obligation, one body node
    /// and one application per argument, and two or three skeleton nodes per
    /// argument; no allocation beyond the pools' growth.
    fn codec(&mut self, spec: Spec, slot: Slot) -> BodyIdx {
        let parts = self.parts(spec);
        let arity = parts.args.len();
        let first_slot = self.slots.len();
        let skeleton = match slot {
            Slot::Plain(var) => self.arena.plans_mut().push_skeleton(SkeletonNode::Var(var)),
            Slot::Root | Slot::Applied(..) => {
                let skeleton = self.arena.plans_mut().push_skeleton(SkeletonNode::Arrow {
                    params: arity as u16 + 1,
                });
                for i in 0..arity {
                    let arg = parts.args.get(i, self.arena);
                    let arg_slot = self.arg_slot(arg);
                    self.slots.push(arg_slot);
                }
                let (param, result) = match slot {
                    Slot::Applied(param, result) => (param, result),
                    Slot::Root => (self.fresh(), self.fresh()),
                    Slot::Plain(_) => unreachable!("handled above"),
                };
                let plans = self.arena.plans_mut();
                plans.push_skeleton(SkeletonNode::Var(param));
                plans.push_skeleton(SkeletonNode::Var(result));
                skeleton
            }
        };
        let plans = self.arena.plans_mut();
        let obligation = plans.push_obligation(Obligation::Value {
            name: parts.name,
            name_loc: parts.name_loc,
            skeleton,
            expr_loc: parts.expr_loc,
            // A plain argument is passed as a value; every other codec is
            // applied, to its arguments or to the binding's parameter.
            called: !matches!(slot, Slot::Plain(_)),
        });
        let mut funct = plans.push_body(BodyNode::Free(obligation));
        for i in 0..arity {
            let arg = parts.args.get(i, self.arena);
            let arg = self.codec(arg, self.slots[first_slot + i]);
            funct = self.arena.plans_mut().push_apply(funct, &[arg], true);
        }
        self.slots.truncate(first_slot);
        funct
    }
}

/// Append the binding `<type><suffix> = v => codec(v)`.
/// Cost: O(codecs of the type); see [`Builder::codec`].
fn binding(
    arena: &mut ParseArena,
    type_name: &str,
    suffix: &str,
    side: Side,
    spec: Spec,
    attributes: Attributes,
    slots: &mut Vec<Slot>,
) {
    let first = arena.plans().next_obligation();
    let mut builder = Builder {
        arena,
        side,
        vars: 0,
        slots,
    };
    let applied = builder.arity(spec) as u32;
    let codec = builder.codec(spec, Slot::Root);
    let vars = builder.vars;
    let name = arena.push_string(format!("{type_name}{suffix}"));
    let param = arena.spice_runtime_v();
    let plans = arena.plans_mut();
    let local = plans.push_body(BodyNode::Local(0));
    let applied_codec = plans.push_apply(codec, &[local], false);
    let body = plans.push_body(BodyNode::Function {
        param,
        body: applied_codec,
    });
    let obligations = Span {
        start: first.0,
        len: plans.next_obligation().0 - first.0,
    };
    plans.push_binding(Binding {
        name,
        attributes,
        obligations,
        body,
        vars,
        ty: TypeSource::ResultOf {
            obligation: first,
            applied,
        },
    });
}

/// Build the plan of a group of declarations that all classify `Plan`: for
/// each, the bindings `generate_codec_decls` makes, in its order.
/// Cost: O(codecs of the manifests); one string per binding name and codec
/// name, as the generator allocates them.
pub(super) fn build(
    arena: &mut ParseArena,
    group: &[TypeDeclaration],
    settings: &[Option<GeneratorSettings>],
) -> DerivedIdx {
    let first = arena.plans().next_binding();
    let mut slots = Vec::new();
    for (decl, settings) in group.iter().zip(settings) {
        let Some(settings) = *settings else {
            continue;
        };
        let type_name = arena.get_string(decl.ptype_name.txt).to_string();
        if let TypeKind::Ptype_record(labels) = &decl.ptype_kind {
            record::bindings(arena, &type_name, labels, settings, &mut slots);
            continue;
        }
        let manifest = decl.ptype_manifest.expect("a planned declaration has a manifest");
        if settings.do_encode {
            let encoder = Spec::Type(manifest, EncodeContext::Optional);
            binding(arena, &type_name, ENCODER_FUNC_SUFFIX, Side::Encode, encoder, Attributes::new(), &mut slots);
            // `manifest_value_encoder`: only a top-level `option` encodes its
            // value differently from its optional form.
            let value_encoder = match default_option_inner_type(arena.get_core_type(manifest), arena) {
                Some(_) => Spec::Type(manifest, EncodeContext::Value),
                None => encoder,
            };
            let attributes = vec![unused_value_warning_attribute(arena)].into();
            binding(arena, &type_name, VALUE_ENCODER_FUNC_SUFFIX, Side::Encode, value_encoder, attributes, &mut slots);
        }
        if settings.do_decode {
            let decoder = Spec::Type(manifest, EncodeContext::Optional);
            binding(arena, &type_name, DECODER_FUNC_SUFFIX, Side::Decode, decoder, Attributes::new(), &mut slots);
        }
    }
    arena.plans_mut().push_item(first)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary_ast::derive;

    /// Parse `source` and run the derive over its top-level items, with
    /// plans.
    fn expand(source: &str) -> (Vec<StructureItem>, ParseArena) {
        expand_on(source, None)
    }

    /// [`expand`], with plans or with every item as syntax.
    fn expand_on(
        source: &str,
        plans_off: Option<GeneralReason>,
    ) -> (Vec<StructureItem>, ParseArena) {
        let mut parser = crate::parser::Parser::new("Test.res", source);
        let items = crate::parser::module::parse_structure(&mut parser);
        assert!(!parser.has_errors(), "{source}");
        let mut arena = parser.into_arena();
        arena.set_derived_plans(plans_off);
        let expanded = items
            .iter()
            .flat_map(|item| {
                derive::expand_structure_item_with_mapper(item, &mut arena, true).unwrap()
            })
            .collect();
        (expanded, arena)
    }

    /// The classification of the last type declaration of `source`.
    fn classification(source: &str) -> Classification {
        let mut parser = crate::parser::Parser::new("Test.res", source);
        let items = crate::parser::module::parse_structure(&mut parser);
        assert!(!parser.has_errors(), "{source}");
        let mut arena = parser.into_arena();
        arena.set_derived_plans(None);
        let (rec_flag, decls) = items
            .iter()
            .rev()
            .find_map(|item| match &item.pstr_desc {
                StructureItemDesc::Pstr_type(inner) => Some((inner.0, &inner.1)),
                _ => None,
            })
            .expect("a type declaration");
        let shares_names = group_shares_names(decls, &arena);
        classify(&arena, decls.last().unwrap(), rec_flag, shares_names)
    }

    #[test]
    fn every_reason_of_the_general_path() {
        use GeneralReason::*;
        let general = |source| match classification(source) {
            Classification::General(reason) => reason,
            Classification::Plan => panic!("{source} takes a plan"),
        };
        assert_eq!(general("@spice type t = array<@spice.codec(c) string>"), CustomCodec);
        assert_eq!(general("@spice type t = {x: @spice.codec(c) int}"), CustomCodec);
        assert_eq!(general("@spice type t = {@spice.default(d) x: int}"), UserExpression);
        assert_eq!(general("@spice type t = {@spice.key(k) x: int}"), UserExpression);
        assert_eq!(general("@spice @spice.fallback(f) type t = string"), UserExpression);
        assert_eq!(general("@spice type t<'a> = array<'a>"), TypeParameters);
        assert_eq!(general("@spice type rec t = array<t>"), RecursiveGroup);
        assert_eq!(general("@spice type a = {x: int} @spice and b = {x: int}"), SharedNames);
        assert_eq!(general("@spice type t = (int, string)"), UnmeasuredShape);
        assert_eq!(general("@spice type t = array<(int, string)>"), UnmeasuredShape);
        assert_eq!(general("@spice type t = [#a | #b]"), UnmeasuredShape);
        assert_eq!(general("@spice.serde type t = A | B"), UnmeasuredShape);
        assert_eq!(general("@spice @unboxed type t = A(int)"), Unboxed);
        assert_eq!(general("@spice type t = {}"), NotYetPlanned);
        assert_eq!(general("@spice type t = {@spice.key(`k`) x: int}"), NotYetPlanned);
        assert_eq!(general("@spice type t = {x: JSON.t}"), NotYetPlanned);
        assert_eq!(general("@spice type t = {x: (int, string)}"), UnmeasuredShape);
        assert_eq!(general("@spice @unboxed type t = {x: int}"), Unboxed);
        assert_eq!(general("@spice type rec t = {x: array<t>}"), RecursiveGroup);
        assert_eq!(general("@spice type t = A | B(int)"), NotYetPlanned);
        assert_eq!(general("@spice type t = JSON.t"), NotYetPlanned);
        assert_eq!(general("@spice type t = array<Js.Json.t>"), NotYetPlanned);
        assert_eq!(general("@spice @spice.fallback(\"x\") type t = string"), NotYetPlanned);
        for planned in [
            "@spice type t = string",
            "@spice type t = array<id>",
            "@spice type t = option<A.t>",
            "@spice.decode type t = result<a, B.c>",
            "@spice type t = dict<option<array<int>>>",
            "@spice type a = string @spice and b = array<a>",
            "@spice type t = {x: int}",
            "@spice type t = {@spice.default(0) x: int, @spice.key(\"k\") y?: string}",
            "@spice.decode type t = {x: option<array<A.t>>}",
            "@spice type a = {x: int} @spice and b = {y: int}",
        ] {
            assert_eq!(classification(planned), Classification::Plan, "{planned}");
        }
    }

    /// Only a group whose derived declarations all take a plan becomes a
    /// plan.
    #[test]
    fn a_group_is_planned_as_a_whole() {
        let derived = |source| {
            let (items, _) = expand(source);
            matches!(items.last().unwrap().pstr_desc, StructureItemDesc::Pstr_derived(_))
        };
        assert!(derived("@spice type a = string @spice and b = array<a>"));
        assert!(derived("type a = {x: int} @spice and b = array<int>"));
        assert!(derived("@spice type a = {x: int} @spice and b = array<a>"));
        assert!(!derived("@spice type a = A | B(int) @spice and b = array<a>"));
    }

    /// With plans off, which a tree is unless the driver says it is compiled
    /// in this process, the classifier keeps every declaration on the
    /// general path, and the seam emits the value group it emitted before
    /// plans.
    #[test]
    fn the_switch_keeps_every_declaration_general() {
        let source = "@spice type a = string @spice and b = array<a>";
        let mut parser = crate::parser::Parser::new("Test.res", source);
        let items = crate::parser::module::parse_structure(&mut parser);
        let mut arena = parser.into_arena();
        let StructureItemDesc::Pstr_type(inner) = &items[0].pstr_desc else {
            panic!("a type declaration")
        };
        for decl in &inner.1 {
            assert_eq!(
                classify(&arena, decl, inner.0, false),
                Classification::General(GeneralReason::Switch)
            );
        }
        let expanded =
            derive::expand_structure_item_with_mapper(&items[0], &mut arena, true)
                .unwrap();
        assert!(matches!(expanded.last().unwrap().pstr_desc, StructureItemDesc::Pstr_value(..)));
        assert_eq!(arena.plans().item_count(), 0);
    }

    #[test]
    fn a_planned_item_allocates_no_general_body() {
        let mut parser = crate::parser::Parser::new("Test.res", "@spice type t = array<string>");
        let items = crate::parser::module::parse_structure(&mut parser);
        let mut arena = parser.into_arena();
        arena.set_derived_plans(None);
        let before = arena.reserve_pat();
        let expanded = derive::expand_structure_item_with_mapper(
            &items[0], &mut arena, true,
        ).unwrap();
        assert!(matches!(expanded[1].pstr_desc, StructureItemDesc::Pstr_derived(_)));
        // Even a single general binding would allocate its parameter and
        // binding patterns. The extra slot is only this test's reservation.
        assert_eq!(arena.reserve_pat().0, before.0 + 1);
        let mut counts = crate::binary_ast::derive::census::SyntaxCounts::default();
        counts.item(&arena, &expanded[1]);
        assert_eq!(counts.bindings, [3, 0]);
        assert_eq!(counts.nodes, [1, 0]);
    }

    fn longident_text(arena: &ParseArena, lid: &Longident) -> String {
        match lid {
            Longident::Lident(name) => arena.get_string(*name).to_string(),
            Longident::Ldot(prefix, name) => {
                format!("{}.{}", longident_text(arena, prefix), arena.get_string(*name))
            }
            Longident::Lapply(_, _) => panic!("no functor application in a codec name"),
        }
    }

    /// The identifiers of an expression in the order inference meets them: a
    /// function's body, then an application's callee before its arguments.
    /// `locals` are the parameters in scope.
    fn identifiers(
        arena: &ParseArena,
        expr: ExprIdx,
        locals: &mut Vec<String>,
        out: &mut Vec<(String, LocIdx, LocIdx)>,
    ) {
        let expr = arena.get_expr(expr);
        match &expr.pexp_desc {
            ExpressionDesc::Pexp_fun(fun) => {
                let PatternDesc::Ppat_var(name) = &arena.get_pat(fun.lhs).ppat_desc else {
                    panic!("a generated function binds a variable")
                };
                locals.push(arena.get_string(name.txt).to_string());
                identifiers(arena, fun.rhs, locals, out);
                locals.pop();
            }
            ExpressionDesc::Pexp_apply(apply) => {
                identifiers(arena, apply.funct, locals, out);
                for (_, arg) in arena.apply_args(apply.args) {
                    identifiers(arena, *arg, locals, out);
                }
            }
            ExpressionDesc::Pexp_ident(lid) => {
                let text = longident_text(arena, arena.get_longident(lid.txt));
                if !locals.contains(&text) {
                    out.push((text, lid.loc, expr.pexp_loc));
                }
            }
            other => panic!("unexpected node in a planned body: {other:?}"),
        }
    }

    /// The obligations of a plan are the free identifiers of its general
    /// form, binding by binding, in typing order, with the same locations.
    #[test]
    fn obligations_follow_the_identifiers_of_the_general_form() {
        for source in [
            "@spice type id = string",
            "@spice type ids = array<id>",
            "@spice type m = option<A.t>",
            "@spice type r = result<array<option<int>>, dict<B.C.t>>",
            "@spice.decode type d = dict<option<list<id>>>\n@spice.encode type e = Null.t<float>",
        ] {
            let (items, arena) = expand(source);
            // The same parse with every item as syntax: the two trees have
            // the same items, and the locations of the source are the same
            // handles in both arenas.
            let (syntax, syntax_arena) =
                expand_on(source, Some(GeneralReason::Switch));
            assert_eq!(items.len(), syntax.len());
            let mut plans = 0;
            for (item, syntax) in items.iter().zip(&syntax) {
                let StructureItemDesc::Pstr_derived(idx) = item.pstr_desc else {
                    continue;
                };
                let StructureItemDesc::Pstr_value((_, general)) = syntax.pstr_desc else {
                    panic!("the general form of a derived item is a value group")
                };
                plans += 1;
                let plan = arena.plans();
                let item = plan.item(idx);
                let general = syntax_arena.vb_list(general);
                assert_eq!(general.len(), plan.bindings(item).len(), "{source}");
                for (binding, vb) in plan.bindings(item).iter().zip(general) {
                    let PatternDesc::Ppat_var(name) = &syntax_arena.get_pat(vb.pvb_pat).ppat_desc
                    else {
                        panic!("a generated binding binds a variable")
                    };
                    assert_eq!(arena.get_string(binding.name), syntax_arena.get_string(name.txt));
                    assert_eq!(
                        binding
                            .attributes
                            .iter()
                            .map(|attr| arena.get_string(attr.0.txt))
                            .collect::<Vec<_>>(),
                        vb.pvb_attributes
                            .iter()
                            .map(|attr| syntax_arena.get_string(attr.0.txt))
                            .collect::<Vec<_>>()
                    );
                    let mut expected = Vec::new();
                    identifiers(&syntax_arena, vb.pvb_expr, &mut Vec::new(), &mut expected);
                    let actual: Vec<_> = binding
                        .obligations
                        .range()
                        .map(|i| {
                            let obligation = plan.obligation(
                                crate::binary_ast::derive::plan::ObligationIdx(i as u32),
                            );
                            let Obligation::Value { name, name_loc, expr_loc, .. } = obligation
                            else {
                                panic!("a constructor application has value obligations only")
                            };
                            let expr_loc = match expr_loc {
                                ExprLoc::OfName => name_loc,
                                ExprLoc::Dummy => arena.dummy_loc(),
                            };
                            (longident_text(&arena, arena.get_longident(name)), name_loc, expr_loc)
                        })
                        .collect();
                    assert_eq!(actual, expected, "{source}: {}", arena.get_string(binding.name));
                }
            }
            assert_eq!(plans, source.matches("@spice").count(), "{source}");
        }
    }

    /// 10,000 nested constructor applications: one obligation and one free
    /// node per constructor, one application per argument, three skeleton
    /// nodes per applied argument.
    #[test]
    fn a_plan_is_linear_in_its_codecs() {
        let depth = 10_000;
        let source = format!("@spice.encode type t = {}int{}", "array<".repeat(depth), ">".repeat(depth));
        let (items, arena) = std::thread::Builder::new()
            .stack_size(256 << 20)
            .spawn(move || expand(&source))
            .unwrap()
            .join()
            .unwrap();
        let StructureItemDesc::Pstr_derived(idx) = items.last().unwrap().pstr_desc else {
            panic!("a plan")
        };
        let plans = arena.plans();
        let bindings = plans.bindings(plans.item(idx));
        assert_eq!(bindings.len(), 2);
        for binding in bindings {
            assert_eq!(binding.obligations.len as usize, depth + 1);
            assert!(matches!(binding.ty, TypeSource::ResultOf { applied: 1, .. }));
            // Root: p, r and the (p, r) of its argument; then two per level;
            // the innermost `int` is a plain name with one variable.
            assert_eq!(binding.vars as usize, 2 + 2 * (depth - 1) + 1);
        }
    }

    /// The plan of the last type declaration of `source`, built whatever the
    /// classifier says, beside the same source expanded to syntax.
    fn record_plan(source: &str) -> (DerivedIdx, ParseArena, Vec<StructureItem>, ParseArena) {
        let mut parser = crate::parser::Parser::new("Test.res", source);
        let items = crate::parser::module::parse_structure(&mut parser);
        assert!(!parser.has_errors(), "{source}");
        let mut arena = parser.into_arena();
        let StructureItemDesc::Pstr_type(inner) = &items.last().unwrap().pstr_desc else {
            panic!("a type declaration")
        };
        let settings: Vec<_> = inner
            .1
            .iter()
            .map(|decl| get_generator_settings_from_attributes(&decl.ptype_attributes, &mut arena).unwrap())
            .collect();
        let idx = build(&mut arena, &inner.1, &settings);
        let (syntax, syntax_arena) = expand_on(source, Some(GeneralReason::Switch));
        (idx, arena, syntax, syntax_arena)
    }

    /// What inference meets in a generated expression, in its order: a
    /// function's body; a callee, then its arguments; an annotation's type,
    /// then its expression; a constructor, then its argument; a record, then
    /// its label; the labels of a record expression, then its values; the
    /// scrutinee of a match, the patterns of all its cases, then their
    /// bodies. A constant with a source location is the user's.
    fn events(arena: &ParseArena, expr: ExprIdx, locals: &mut Vec<String>, out: &mut Vec<String>) {
        let expr = arena.get_expr(expr);
        let type_name = |typ: CoreTypeIdx| {
            let CoreTypeDesc::Ptyp_constr((lid, _)) = &arena.get_core_type(typ).ptyp_desc else {
                panic!("a generated annotation names a type")
            };
            format!("type {} {:?}", longident_text(arena, arena.get_longident(lid.txt)), lid.loc)
        };
        let name = |lid: &Located<LidentIdx>| {
            format!("{} {:?}", longident_text(arena, arena.get_longident(lid.txt)), lid.loc)
        };
        match &expr.pexp_desc {
            ExpressionDesc::Pexp_fun(fun) => {
                let PatternDesc::Ppat_var(param) = &arena.get_pat(fun.lhs).ppat_desc else {
                    panic!("a generated function binds a variable")
                };
                locals.push(arena.get_string(param.txt).to_string());
                events(arena, fun.rhs, locals, out);
                locals.pop();
            }
            ExpressionDesc::Pexp_apply(apply) => {
                events(arena, apply.funct, locals, out);
                for (_, arg) in arena.apply_args(apply.args) {
                    events(arena, *arg, locals, out);
                }
            }
            ExpressionDesc::Pexp_ident(lid) => {
                let text = longident_text(arena, arena.get_longident(lid.txt));
                if !locals.contains(&text) {
                    out.push(format!("value {text} {:?} {:?}", lid.loc, expr.pexp_loc));
                }
            }
            ExpressionDesc::Pexp_constraint(inner) => {
                out.push(type_name(inner.1));
                events(arena, inner.0, locals, out);
            }
            ExpressionDesc::Pexp_construct(lid, args) => {
                out.push(format!("construct {}", name(lid)));
                for arg in arena.expr_list(args.txt) {
                    events(arena, *arg, locals, out);
                }
            }
            ExpressionDesc::Pexp_field(record, lid) => {
                events(arena, *record, locals, out);
                out.push(format!("access {}", name(lid)));
            }
            ExpressionDesc::Pexp_record((fields, None)) => {
                let fields = arena.expr_field_list(*fields);
                for field in fields {
                    out.push(format!("field {}", name(&field.lid)));
                }
                for field in fields {
                    events(arena, field.expr, locals, out);
                }
            }
            ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => {
                for item in arena.expr_list(*items) {
                    events(arena, *item, locals, out);
                }
            }
            ExpressionDesc::Pexp_constant(_) => {
                if expr.pexp_loc != arena.none_loc() && expr.pexp_loc != arena.dummy_loc() {
                    let literal = format!("literal {:?}", expr.pexp_loc);
                    if !out.contains(&literal) {
                        out.push(literal);
                    }
                }
            }
            ExpressionDesc::Pexp_match((scrutinee, cases)) => {
                events(arena, *scrutinee, locals, out);
                let cases = arena.case_list(*cases);
                let mut binders = Vec::new();
                for case in cases {
                    let mut pattern = arena.get_pat(case.pc_lhs);
                    let mut binder = None;
                    loop {
                        match &pattern.ppat_desc {
                            PatternDesc::Ppat_construct(lid, args) => {
                                out.push(format!("pattern {}", name(lid)));
                                let [arg] = arena.pat_list(args.txt) else {
                                    panic!("a generated pattern has one argument")
                                };
                                pattern = arena.get_pat(*arg);
                            }
                            PatternDesc::Ppat_constraint(inner) => {
                                out.push(type_name(inner.1));
                                pattern = arena.get_pat(inner.0);
                            }
                            PatternDesc::Ppat_var(var) => {
                                binder = Some(arena.get_string(var.txt).to_string());
                                break;
                            }
                            PatternDesc::Ppat_any => break,
                            other => panic!("unexpected generated pattern: {other:?}"),
                        }
                    }
                    binders.push(binder);
                }
                for (case, binder) in cases.iter().zip(binders) {
                    let bound = binder.is_some();
                    locals.extend(binder);
                    events(arena, case.pc_rhs, locals, out);
                    if bound {
                        locals.pop();
                    }
                }
            }
            other => panic!("unexpected node in a planned body: {other:?}"),
        }
    }

    /// The obligations of a record's plan are what inference meets in its
    /// general form, binding by binding, in typing order, with the same
    /// names and locations.
    #[test]
    fn record_obligations_follow_the_general_form() {
        for source in [
            "@spice type t = {x: int}",
            "@spice type t = {label: string, value: array<option<A.t>>}",
            "@spice type t = {a: option<string>, b?: int, c: Null.t<float>}",
            "@spice type t = {@spice.key(\"k\") a: int, @spice.default(0) b: int, @spice.default(1.5) c: float, d?: bool}",
            "@spice.decode type d = {@spice.key(\"other\") x: dict<id>, y?: array<int>}",
        ] {
            let run = move || {
                let (idx, arena, syntax, syntax_arena) = record_plan(source);
                let StructureItemDesc::Pstr_value((_, general)) = syntax.last().unwrap().pstr_desc
                else {
                    panic!("the general form of a derived item is a value group")
                };
                let plans = arena.plans();
                let bindings = plans.bindings(plans.item(idx));
                let general = syntax_arena.vb_list(general);
                assert_eq!(general.len(), bindings.len(), "{source}");
                for (binding, vb) in bindings.iter().zip(general) {
                    let PatternDesc::Ppat_var(name) = &syntax_arena.get_pat(vb.pvb_pat).ppat_desc
                    else {
                        panic!("a generated binding binds a variable")
                    };
                    assert_eq!(arena.get_string(binding.name), syntax_arena.get_string(name.txt));
                    assert_eq!(binding.attributes.len(), vb.pvb_attributes.len());
                    assert!(matches!(binding.ty, TypeSource::Stated(_)));
                    let mut expected = Vec::new();
                    events(&syntax_arena, vb.pvb_expr, &mut Vec::new(), &mut expected);
                    let text = |name: LidentIdx| longident_text(&arena, arena.get_longident(name));
                    let (none, dummy) = (arena.none_loc(), arena.dummy_loc());
                    let actual: Vec<String> = binding
                        .obligations
                        .range()
                        .map(|i| match plans.obligation(ObligationIdx(i as u32)) {
                            Obligation::Value { name, name_loc, expr_loc, .. } => {
                                let expr_loc = match expr_loc {
                                    ExprLoc::OfName => name_loc,
                                    ExprLoc::Dummy => dummy,
                                };
                                format!("value {} {name_loc:?} {expr_loc:?}", text(name))
                            }
                            Obligation::Type { name, name_loc, .. } => {
                                format!("type {} {name_loc:?}", text(name))
                            }
                            Obligation::Label { name, usage, .. } => match usage {
                                LabelUse::Access => format!("access {} {none:?}", text(name)),
                                LabelUse::AccessDummy => format!("access {} {dummy:?}", text(name)),
                                LabelUse::Construct => format!("field {} {none:?}", text(name)),
                            },
                            Obligation::Constructor { name, site, .. } => match site {
                                Site::Construct => format!("construct {} {dummy:?}", text(name)),
                                Site::Pattern => format!("pattern {} {none:?}", text(name)),
                                Site::PatternDummy => format!("pattern {} {dummy:?}", text(name)),
                            },
                            Obligation::Literal { expr, .. } => {
                                format!("literal {:?}", arena.get_expr(expr).pexp_loc)
                            }
                        })
                        .collect();
                    assert_eq!(actual, expected, "{source}: {}", arena.get_string(binding.name));
                }
            };
            std::thread::Builder::new()
                .stack_size(64 << 20)
                .spawn(run)
                .unwrap()
                .join()
                .unwrap();
        }
    }

    /// A record of 10,000 fields: per field three obligations and seven body
    /// nodes in an encoder, sixteen obligations and thirty-two body nodes in
    /// its decoder, beside a fixed number per binding.
    #[test]
    fn a_record_plan_is_linear_in_its_fields() {
        let fields = 10_000;
        let source = format!(
            "@spice type t = {{{}}}",
            (0..fields).map(|i| format!("f{i}: int")).collect::<Vec<_>>().join(", ")
        );
        let mut parser = crate::parser::Parser::new("Test.res", &source);
        let items = crate::parser::module::parse_structure(&mut parser);
        assert!(!parser.has_errors());
        let mut arena = parser.into_arena();
        let StructureItemDesc::Pstr_type(inner) = &items[0].pstr_desc else {
            panic!("a type declaration")
        };
        let settings =
            [get_generator_settings_from_attributes(&inner.1[0].ptype_attributes, &mut arena).unwrap()];
        let idx = build(&mut arena, &inner.1, &settings);
        let plans = arena.plans();
        let bindings = plans.bindings(plans.item(idx));
        let obligations: Vec<_> = bindings.iter().map(|binding| binding.obligations.len as usize).collect();
        assert_eq!(obligations, [4 + 3 * fields, 4 + 3 * fields, 4 + 16 * fields]);
        assert_eq!(plans.body_count(), 2 * (10 + 7 * fields) + 12 + 32 * fields);
    }
}
