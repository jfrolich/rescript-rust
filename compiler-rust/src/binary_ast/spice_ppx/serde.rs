//! Codecs for `@spice.serde` variants and polymorphic variants, which encode
//! the way Rust's serde derive does. Port of ppx_spice `src/ppx/serde.ml`
//! (jfrolich/ppx_spice 0.9.0) and the serde parts of `utils.ml`,
//! `variants.ml` and `polyvariants.ml`.

use super::*;

/// utils.ml `serde`: without a tag, externally tagged; with ReScript's
/// `@tag("type")` on the type, internally tagged. `legacy` decoders also read
/// the default spice encoding; `legacy_write` encoders write it (and implies
/// `legacy`).
#[derive(Clone, Copy, Debug)]
pub(super) struct Serde {
    pub tag: Option<StrIdx>,
    pub legacy: bool,
    pub legacy_write: bool,
}

/// serde.ml `payload`.
pub(super) enum CasePayload {
    Unit,
    Args(Vec<CoreType>),
    Record(Vec<LabelDeclaration>),
}

/// How a case builds its value: `Exp.construct` or `Exp.variant`.
pub(super) enum Construct {
    Variant(StrIdx),
    Poly(Cow<'static, str>),
}

impl Construct {
    fn build(&self, arg: Option<Expression>, arena: &mut ParseArena) -> Expression {
        match self {
            Construct::Variant(name) => {
                let lid = arena.push_lident_from_idx(*name);
                expr_construct(lid, arg, arena)
            }
            Construct::Poly(label) => expr_variant(label.clone(), arg, arena),
        }
    }
}

/// serde.ml `case`.
pub(super) struct SerdeCase {
    /// The name in JSON: the constructor, or its `@spice.as` string.
    pub name: String,
    /// The ReScript constructor.
    pub constructor: StrIdx,
    /// `@spice.alias("...")`: other names it decodes from.
    pub aliases: Vec<String>,
    /// `@spice.other`: a unit constructor any unknown name decodes to.
    pub other: bool,
    /// `@spice.untagged`: a one-value constructor written as its value alone.
    pub untagged: bool,
    pub payload: CasePayload,
    /// The constructor pattern, binding `v0`, `v1`, ... or the record fields.
    pub lhs: Pattern,
    pub construct: Construct,
}

// ---------------------------------------------------------------------------
// Attributes (utils.ml)
// ---------------------------------------------------------------------------

fn payload_is_empty(attr: &Attribute) -> bool {
    matches!(&attr.1, Payload::PStr(items) if items.is_empty())
}

fn bool_value(expr: &Expression, arena: &ParseArena) -> Option<bool> {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_construct(lid, args) if args.txt.is_empty() => {
            if longident_matches(arena, lid.txt, &["true"]) {
                Some(true)
            } else if longident_matches(arena, lid.txt, &["false"]) {
                Some(false)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// utils.ml `get_serde_legacy`: `(legacy, legacy_write)`.
fn get_serde_legacy(attr: &Attribute, arena: &ParseArena) -> SpiceResult<(bool, bool)> {
    let invalid =
        || "@spice.serde takes no payload, {legacy: bool} or {legacyWrite: bool}".to_string();
    if payload_is_empty(attr) {
        return Ok((false, false));
    }
    let expr = get_expression_from_payload(attr, arena)?;
    let ExpressionDesc::Pexp_record(record) = &expr.pexp_desc else {
        return Err(invalid());
    };
    let (fields, spread) = &*record;
    if spread.is_some() || fields.len() != 1 {
        return Err(invalid());
    }
    let field = &arena.expr_field_list(*fields)[0];
    let value = arena.get_expr(field.expr);
    if longident_matches(arena, field.lid.txt, &["legacy"]) {
        let legacy = bool_value(value, arena).ok_or_else(invalid)?;
        Ok((legacy, false))
    } else if longident_matches(arena, field.lid.txt, &["legacyWrite"]) {
        let write = bool_value(value, arena).ok_or_else(invalid)?;
        Ok((write, write))
    } else {
        Err(invalid())
    }
}

/// utils.ml `get_string_payload`.
fn get_string_payload(attr: &Attribute, arena: &mut ParseArena) -> SpiceResult<StrIdx> {
    let expr = get_expression_from_payload(attr, arena)?;
    match super::alias_string_semantic(&expr, arena) {
        Some(semantic) => Ok(arena.intern_string(&semantic)),
        _ => Err("Expected a string as attribute payload".to_string()),
    }
}

/// utils.ml `get_serde_from_attributes`.
pub(super) fn get_serde_from_attributes(
    attrs: &[Attribute],
    arena: &mut ParseArena,
) -> SpiceResult<Option<Serde>> {
    let Some(serde) = get_attribute_by_name(attrs, "spice.serde", arena)? else {
        return Ok(None);
    };
    let (legacy, legacy_write) = get_serde_legacy(serde, arena)?;
    let tag = match get_attribute_by_name(attrs, "tag", arena)? {
        None => None,
        Some(attr) => Some(get_string_payload(attr, arena)?),
    };
    Ok(Some(Serde {
        tag,
        legacy,
        legacy_write,
    }))
}

fn string_of_expr(expr: &Expression, arena: &ParseArena) -> Option<String> {
    super::alias_string_semantic(expr, arena)
}

/// serde.ml `name_of_alias`.
pub(super) fn name_of_alias(
    has_attr_as: bool,
    alias: &Expression,
    constructor: &str,
    arena: &ParseArena,
) -> SpiceResult<String> {
    if !has_attr_as {
        return Ok(constructor.to_string());
    }
    string_of_expr(alias, arena)
        .ok_or_else(|| "@spice.serde needs @spice.as to be a string".to_string())
}

/// serde.ml `name_of_attributes`: a constructor's JSON name is its
/// `@spice.as`, else ReScript's `@as` (kept as `pcd_runtime_tag`), else the
/// constructor.
fn name_of_variant(decl: &ParsedVariantDecl, arena: &ParseArena) -> SpiceResult<String> {
    let constructor = arena.get_string(decl.name);
    let spice_name = name_of_alias(decl.has_attr_as, &decl.alias, constructor, arena)?;
    match &decl.constr_decl.pcd_runtime_tag {
        None => Ok(spice_name),
        Some(tag) => match &tag.txt {
            crate::parser::ast::ConstructorTag::Pct_string(s) => {
                let s = s.semantic(arena);
                if decl.has_attr_as && s != spice_name {
                    Err("@as and @spice.as name the constructor differently".to_string())
                } else {
                    Ok(s.to_string())
                }
            }
            _ => Err("@spice.serde needs @as to be a string".to_string()),
        },
    }
}

/// serde.ml `flags_of_attributes`: `(aliases, other, untagged)`.
pub(super) fn flags_of_attributes(
    attrs: &[Attribute],
    arena: &ParseArena,
) -> SpiceResult<(Vec<String>, bool, bool)> {
    let named = |name: &str| -> Vec<&Attribute> {
        attrs
            .iter()
            .filter(|attr| {
                arena
                    .get_string(attr.0.txt)
                    .strip_prefix("spice.")
                    .is_some_and(|rest| rest == name)
            })
            .collect()
    };
    let flag = |name: &str| -> SpiceResult<bool> {
        match named(name).as_slice() {
            [] => Ok(false),
            [attr] if payload_is_empty(attr) => Ok(true),
            [_] => Err(format!("@spice.{name} takes no payload")),
            _ => Err(format!("Too many occurrences of @spice.{name}")),
        }
    };
    // OCaml evaluates the tuple right to left.
    let untagged = flag("untagged")?;
    let other = flag("other")?;
    let mut aliases = Vec::new();
    for attr in named("alias") {
        let expr = get_expression_from_payload(attr, arena)?;
        aliases.push(
            string_of_expr(&expr, arena)
                .ok_or_else(|| "@spice.alias needs a string".to_string())?,
        );
    }
    Ok((aliases, other, untagged))
}

/// serde.ml `reject_flags`.
pub(super) fn reject_flags(attrs: &[Attribute], arena: &ParseArena) -> SpiceResult<()> {
    match flags_of_attributes(attrs, arena)? {
        (aliases, false, false) if aliases.is_empty() => Ok(()),
        _ => Err("@spice.alias, @spice.other and @spice.untagged need @spice.serde".to_string()),
    }
}

// ---------------------------------------------------------------------------
// Expression helpers
// ---------------------------------------------------------------------------

/// serde.ml `str`: a `{*j|...|*j}` string, read back as source text.
fn str_expr(arena: &mut ParseArena, s: &str) -> Expression {
    let constant = match crate::string_literal::string_from_source(s) {
        Some(literal) => Constant::String(arena.push_string_literal(&literal)),
        None => arena.string_constant(s),
    };
    expr_constant(constant, arena)
}

fn int_expr(arena: &mut ParseArena, i: usize) -> Expression {
    expr_constant(
        Constant::Integer(arena.intern_string(&i.to_string()), None),
        arena,
    )
}

fn ident(arena: &mut ParseArena, name: &str) -> Expression {
    expr_ident_path(arena, &[name])
}

/// utils.ml `make_ident_expr`: `Exp.ident (mknoloc ...)`.
fn noloc_ident(arena: &mut ParseArena, name: &str) -> Expression {
    let lid_idx = lident_path_parse(arena, &[name]);
    expr_ident_with_loc(lid_idx, arena.none_loc(), arena.dummy_loc())
}

fn lid(arena: &mut ParseArena, name: &str) -> LidentIdx {
    let name = arena.intern_string(name);
    arena.push_lident_from_idx(name)
}

fn construct(arena: &mut ParseArena, name: &str, arg: Option<Expression>) -> Expression {
    let lid = lid(arena, name);
    let loc = arena.dummy_loc();
    expr_construct_with_loc(lid, arg, loc, arena)
}

fn pconstruct(arena: &mut ParseArena, name: &str, arg: Option<Pattern>) -> Pattern {
    let lid = lid(arena, name);
    let loc = arena.dummy_loc();
    pat_construct_with_loc(lid, arg, loc, arena)
}

fn json_construct(arena: &mut ParseArena, ctor: &str, arg: Option<Expression>) -> Expression {
    let lid = lident_path_static(arena, &["JSON", ctor]);
    let loc = arena.dummy_loc();
    expr_construct_with_loc(lid, arg, loc, arena)
}

fn json_pattern(arena: &mut ParseArena, ctor: &str, arg: Option<Pattern>) -> Pattern {
    let lid = lident_path_static(arena, &["JSON", ctor]);
    let loc = arena.dummy_loc();
    pat_construct_with_loc(lid, arg, loc, arena)
}

fn apply(arena: &mut ParseArena, func: Expression, args: Vec<Expression>) -> Expression {
    let args = args
        .into_iter()
        .map(|arg| (ArgLabel::Nolabel, arg))
        .collect();
    expr_apply(func, args, false, arena.dummy_loc(), arena)
}

fn spice_error(arena: &mut ParseArena, message: &str, value: Expression) -> Expression {
    let message = expr_constant_literal(arena, message);
    expr_spice_error_variants(arena, message, value, None)
}

fn arg_names(count: usize) -> Vec<String> {
    (0..count).map(|i| format!("v{i}")).collect()
}

/// serde.ml `args_pattern`.
pub(super) fn args_pattern(count: usize, arena: &mut ParseArena) -> Option<Pattern> {
    if count == 0 {
        return None;
    }
    let vars = arg_names(count)
        .iter()
        .map(|name| pat_var_none(arena, name))
        .collect();
    Some(tuple_or_singleton_pat(vars, arena))
}

/// serde.ml `json_object`.
fn json_object(entries: Vec<Expression>, arena: &mut ParseArena) -> Expression {
    let array = expr_array(entries, arena);
    let from_array = expr_ident_path(arena, &["Dict", "fromArray"]);
    let dict = apply(arena, from_array, vec![array]);
    let object = json_construct(arena, "Object", Some(dict));
    expr_constraint(object, ctyp_json_t_const(arena), arena)
}

/// `match (v : JSON.t) with ...` constraint.
fn json_typed(arena: &mut ParseArena, name: &str) -> Expression {
    let value = ident(arena, name);
    expr_constraint(value, ctyp_json_t(arena), arena)
}

// ---------------------------------------------------------------------------
// Validation
// ---------------------------------------------------------------------------

fn validate_names(cases: &[SerdeCase]) -> SpiceResult<()> {
    let mut seen: Vec<&str> = Vec::new();
    for case in cases.iter().filter(|case| !case.untagged) {
        for name in std::iter::once(&case.name).chain(case.aliases.iter()) {
            if seen.contains(&name.as_str()) {
                return Err(format!("Two constructors are both named {name} in JSON"));
            }
            seen.push(name);
        }
    }
    Ok(())
}

fn validate_flags(cases: &[SerdeCase]) -> SpiceResult<()> {
    let others: Vec<&SerdeCase> = cases.iter().filter(|case| case.other).collect();
    let untagged: Vec<&SerdeCase> = cases.iter().filter(|case| case.untagged).collect();
    if others.len() > 1 {
        return Err("Only one constructor can be @spice.other".to_string());
    }
    for case in &others {
        if !matches!(case.payload, CasePayload::Unit) {
            return Err("@spice.other needs a constructor without payload".to_string());
        }
    }
    for case in &untagged {
        if !matches!(&case.payload, CasePayload::Args(args) if args.len() == 1) {
            return Err("@spice.untagged needs a constructor with one value".to_string());
        }
        if !case.aliases.is_empty() {
            return Err("An @spice.untagged constructor has no name to alias".to_string());
        }
    }
    if !others.is_empty() && !untagged.is_empty() {
        return Err("@spice.other and @spice.untagged can't be combined".to_string());
    }
    Ok(())
}

fn validate(tag: Option<&str>, cases: &[SerdeCase], arena: &mut ParseArena) -> SpiceResult<()> {
    validate_names(cases)?;
    validate_flags(cases)?;
    let Some(tag) = tag else {
        return Ok(());
    };
    for case in cases {
        match &case.payload {
            CasePayload::Unit => {}
            CasePayload::Args(args) if args.len() == 1 => {}
            CasePayload::Args(_) => {
                return Err(
                    "An internally tagged (@tag) @spice.serde constructor can't have \
                            several payload values, like serde's #[serde(tag = ...)]; use an \
                            inline record, or one value that encodes to an object"
                        .to_string(),
                );
            }
            CasePayload::Record(fields) => {
                for field in fields {
                    let txt = arena.get_string(field.pld_name.txt).to_string();
                    let key = match get_attribute_by_name(&field.pld_attributes, "spice.key", arena)
                    {
                        Ok(Some(attr)) => {
                            let expr = get_expression_from_payload(attr, arena)?;
                            match &expr.pexp_desc {
                                ExpressionDesc::Pexp_constant(c) => match &*c {
                                    Constant::String(s) => s.semantic(arena).to_string(),
                                    _ => txt,
                                },
                                _ => txt,
                            }
                        }
                        _ => txt,
                    };
                    if key == tag {
                        return Err(format!("A payload field is keyed like the tag {tag}"));
                    }
                }
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Encoder
// ---------------------------------------------------------------------------

fn encode_arg(
    settings: GeneratorSettings,
    arg: &CoreType,
    name: &str,
    arena: &mut ParseArena,
) -> SpiceResult<Expression> {
    let (encoder, _) = codecs_generate_value_codecs(settings, arg, arena)?;
    let encoder = require_encoder(encoder)?;
    let value = noloc_ident(arena, name);
    Ok(apply(arena, encoder, vec![value]))
}

fn encoder_case(
    settings: GeneratorSettings,
    tag: Option<&str>,
    case: &SerdeCase,
    arena: &mut ParseArena,
) -> SpiceResult<Case> {
    let name = case.name.as_str();
    let rhs = match (&case.payload, tag) {
        (CasePayload::Args(args), _) if case.untagged && args.len() == 1 => {
            encode_arg(settings, &args[0], "v0", arena)?
        }
        (CasePayload::Unit, None) => {
            let name = str_expr(arena, name);
            json_construct(arena, "String", Some(name))
        }
        (CasePayload::Unit, Some(tag)) => {
            let key = str_expr(arena, tag);
            let name = str_expr(arena, name);
            let value = json_construct(arena, "String", Some(name));
            let entry = expr_tuple(vec![key, value], arena);
            json_object(vec![entry], arena)
        }
        (CasePayload::Args(args), Some(tag)) => {
            let func = expr_ident_path(arena, &["Spice", "taggedObject"]);
            let tag = str_expr(arena, tag);
            let name = str_expr(arena, name);
            let value = encode_arg(settings, &args[0], "v0", arena)?;
            apply(arena, func, vec![tag, name, value])
        }
        (CasePayload::Args(args), None) => {
            let mut values = Vec::with_capacity(args.len());
            for (arg, var) in args.iter().zip(arg_names(args.len())) {
                values.push(encode_arg(settings, arg, &var, arena)?);
            }
            let value = if values.len() == 1 {
                values.pop().expect("one value")
            } else {
                let array = expr_array(values, arena);
                json_construct(arena, "Array", Some(array))
            };
            let key = str_expr(arena, name);
            let entry = expr_tuple(vec![key, value], arena);
            json_object(vec![entry], arena)
        }
        (CasePayload::Record(fields), None) => {
            let key = str_expr(arena, name);
            let value = records_generate_inline_encoder_expr(settings, fields, vec![], arena)?;
            let entry = expr_tuple(vec![key, value], arena);
            json_object(vec![entry], arena)
        }
        (CasePayload::Record(fields), Some(tag)) => {
            let key = str_expr(arena, tag);
            let name = str_expr(arena, name);
            let value = json_construct(arena, "String", Some(name));
            let some = construct(arena, "Some", Some(value));
            let leading = expr_tuple(vec![key, some], arena);
            records_generate_inline_encoder_expr(settings, fields, vec![leading], arena)?
        }
    };
    Ok(super::case(case.lhs.clone(), rhs, arena))
}

fn generate_encoder(
    settings: GeneratorSettings,
    tag: Option<&str>,
    cases: &[SerdeCase],
    arena: &mut ParseArena,
) -> SpiceResult<Expression> {
    let mut match_cases = Vec::with_capacity(cases.len());
    for case in cases {
        match_cases.push(encoder_case(settings, tag, case, arena)?);
    }
    let v = ident(arena, "v");
    let match_expr = expr_match(v, match_cases, arena);
    let constrained = expr_constraint(match_expr, ctyp_json_t_const(arena), arena);
    Ok(expr_fun(
        ArgLabel::Nolabel,
        pat_var_dummy(arena, "v"),
        constrained,
        Some(1),
        arena,
    ))
}

// ---------------------------------------------------------------------------
// Decoder
// ---------------------------------------------------------------------------

/// serde.ml `with_path`.
fn with_path(prefix: &str, expr: Expression, arena: &mut ParseArena) -> Expression {
    let prefix = str_expr(arena, prefix);
    prefix_decode_error_path(expr, prefix, arena)
}

fn decoder_of(
    settings: GeneratorSettings,
    arg: &CoreType,
    arena: &mut ParseArena,
) -> SpiceResult<Expression> {
    let (_, decoder) = codecs_generate_value_codecs(settings, arg, arena)?;
    require_decoder(decoder)
}

/// serde.ml `decode_args`.
fn decode_args(
    settings: GeneratorSettings,
    case: &SerdeCase,
    args: &[CoreType],
    arena: &mut ParseArena,
) -> SpiceResult<Expression> {
    if args.len() == 1 {
        let decoder = decoder_of(settings, &args[0], arena)?;
        let payload = ident(arena, "payload");
        let decoded = apply(arena, decoder, vec![payload]);
        let ok_pat = {
            let var = pat_var_dummy(arena, "v0");
            pconstruct(arena, "Ok", Some(var))
        };
        let ok_rhs = {
            let v0 = noloc_ident(arena, "v0");
            let value = case.construct.build(Some(v0), arena);
            construct(arena, "Ok", Some(value))
        };
        let error_pat = {
            let var = pat_var_dummy(arena, "e");
            pconstruct(arena, "Error", Some(var))
        };
        let error_rhs = {
            let e = ident(arena, "e");
            construct(arena, "Error", Some(e))
        };
        let cases = vec![
            super::case(ok_pat, ok_rhs, arena),
            super::case(error_pat, error_rhs, arena),
        ];
        return Ok(expr_match(decoded, cases, arena));
    }
    let count = args.len();
    let names = arg_names(count);
    let success = {
        let pats = names
            .iter()
            .map(|name| {
                let var = pat_var_none(arena, name);
                pconstruct(arena, "Ok", Some(var))
            })
            .collect();
        let lhs = tuple_or_singleton_pat(pats, arena);
        let values = names.iter().map(|name| noloc_ident(arena, name)).collect();
        let values = tuple_or_singleton_expr(values, arena);
        let value = case.construct.build(Some(values), arena);
        let rhs = construct(arena, "Ok", Some(value));
        super::case(lhs, rhs, arena)
    };
    let mut match_cases = vec![success];
    for i in 0..count {
        match_cases.push(generate_error_case(count, i, false, arena));
    }
    let mut decoded = Vec::with_capacity(count);
    for (i, arg) in args.iter().enumerate() {
        let decoder = decoder_of(settings, arg, arena)?;
        let get = expr_ident_path(arena, &["Array", "getUnsafe"]);
        let json_arr = ident(arena, "json_arr");
        let index = int_expr(arena, i);
        let item = apply(arena, get, vec![json_arr, index]);
        decoded.push(apply(arena, decoder, vec![item]));
    }
    let decoded = tuple_or_singleton_expr(decoded, arena);
    let decoded = expr_match(decoded, match_cases, arena);
    let length = {
        let func = expr_ident_path(arena, &["Array", "length"]);
        let json_arr = ident(arena, "json_arr");
        apply(arena, func, vec![json_arr])
    };
    let expected = int_expr(arena, count);
    let cond = expr_not_equal(arena, length, expected);
    let arity_error = {
        let payload = ident(arena, "payload");
        spice_error(
            arena,
            "Invalid number of arguments to variant constructor",
            payload,
        )
    };
    let checked = expr_ifthenelse(cond, arity_error, Some(decoded), arena);
    let array_pat = {
        let var = pat_var_dummy(arena, "json_arr");
        json_pattern(arena, "Array", Some(var))
    };
    let not_array = {
        let payload = ident(arena, "payload");
        spice_error(arena, "Not an array", payload)
    };
    let cases = vec![
        super::case(array_pat, checked, arena),
        super::case(pat_any(arena), not_array, arena),
    ];
    let payload = ident(arena, "payload");
    Ok(expr_match(payload, cases, arena))
}

/// serde.ml `decode_by_name`.
fn decode_by_name(
    cases: Vec<(String, Expression)>,
    otherwise: Expression,
    arena: &mut ParseArena,
) -> Expression {
    let mut acc = otherwise;
    for (name, decoded) in cases.into_iter().rev() {
        let spice_tag = ident(arena, "spice_tag");
        let name = str_expr(arena, &name);
        // `[%expr spice_tag = ...]`: the operator at the quotation's location.
        let op = expr_ident_path(arena, &["=="]);
        let cond = apply(arena, op, vec![spice_tag, name]);
        acc = expr_ifthenelse(cond, decoded, Some(acc), arena);
    }
    acc
}

/// serde.ml `decode_untagged`.
fn decode_untagged(
    settings: GeneratorSettings,
    cases: &[&SerdeCase],
    error: Expression,
    arena: &mut ParseArena,
) -> SpiceResult<Expression> {
    let Some((case, rest)) = cases.split_first() else {
        return Ok(error);
    };
    let CasePayload::Args(args) = &case.payload else {
        return Err("@spice.untagged needs a constructor with one value".to_string());
    };
    let [arg] = args.as_slice() else {
        return Err("@spice.untagged needs a constructor with one value".to_string());
    };
    let decoder = decoder_of(settings, arg, arena)?;
    let v = ident(arena, "v");
    let decoded = apply(arena, decoder, vec![v]);
    let ok_pat = {
        let var = pat_var_dummy(arena, "v0");
        pconstruct(arena, "Ok", Some(var))
    };
    let ok_rhs = {
        let v0 = ident(arena, "v0");
        let value = case.construct.build(Some(v0), arena);
        construct(arena, "Ok", Some(value))
    };
    let error_pat = {
        let any = pat_any(arena);
        pconstruct(arena, "Error", Some(any))
    };
    let error_rhs = decode_untagged(settings, rest, error, arena)?;
    let cases = vec![
        super::case(ok_pat, ok_rhs, arena),
        super::case(error_pat, error_rhs, arena),
    ];
    Ok(expr_match(decoded, cases, arena))
}

/// `pat as name`.
fn pat_alias(pat: Pattern, name: &str, arena: &mut ParseArena) -> Pattern {
    let name = arena.intern_string(name);
    Pattern {
        ppat_desc: PatternDesc::Ppat_alias(
            arena.push_pat(pat),
            Located::new(name, arena.dummy_loc()),
        ),
        ppat_loc: arena.dummy_loc(),
        ppat_attributes: Attributes::new(),
    }
}

fn ok_construct_none(case: &SerdeCase, arena: &mut ParseArena) -> Expression {
    let value = case.construct.build(None, arena);
    construct(arena, "Ok", Some(value))
}

/// serde.ml `generate_decoder`.
fn generate_decoder(
    settings: GeneratorSettings,
    tag: Option<&str>,
    legacy: Option<Expression>,
    all_cases: &[SerdeCase],
    arena: &mut ParseArena,
) -> SpiceResult<Expression> {
    // serde writes a unit constructor as a bare string only when externally
    // tagged; an internally tagged one reads it only as a legacy value.
    let string_decodes = tag.is_none() || legacy.is_some();
    let untagged: Vec<&SerdeCase> = all_cases.iter().filter(|case| case.untagged).collect();
    let cases: Vec<&SerdeCase> = all_cases.iter().filter(|case| !case.untagged).collect();
    let other = cases.iter().copied().find(|case| case.other);

    let invalid = |arena: &mut ParseArena| match other {
        Some(case) => ok_construct_none(case, arena),
        None => {
            let v = ident(arena, "v");
            spice_error(arena, "Invalid variant constructor", v)
        }
    };

    // [(name, decoded)] for every JSON name a case reads, its aliases too.
    let mut units = Vec::new();
    for case in &cases {
        if matches!(case.payload, CasePayload::Unit) {
            for name in std::iter::once(&case.name).chain(case.aliases.iter()) {
                units.push((name.clone(), ok_construct_none(case, arena)));
            }
        }
    }
    // As serde: a bare string naming a constructor with a payload is an
    // error, not the `@spice.other` constructor.
    let mut names = units.clone();
    if other.is_some() {
        for case in &cases {
            if !matches!(case.payload, CasePayload::Unit) {
                for name in std::iter::once(&case.name).chain(case.aliases.iter()) {
                    let v = ident(arena, "v");
                    names.push((
                        name.clone(),
                        spice_error(arena, "Invalid variant constructor", v),
                    ));
                }
            }
        }
    }
    // As serde: an unknown name keyed to anything but null is an error.
    let unknown_key = |arena: &mut ParseArena| match other {
        Some(case) => {
            let null_pat = json_pattern(arena, "Null", None);
            let ok = ok_construct_none(case, arena);
            let dot = str_expr(arena, ".");
            let spice_tag = ident(arena, "spice_tag");
            let path = expr_concat(arena, dot, spice_tag);
            let message = expr_constant_literal(arena, "Expected null");
            let payload = ident(arena, "payload");
            let error = expr_spice_error_variants(arena, message, payload, Some(path));
            let cases = vec![
                super::case(null_pat, ok, arena),
                super::case(pat_any(arena), error, arena),
            ];
            let payload = ident(arena, "payload");
            expr_match(payload, cases, arena)
        }
        None => invalid(arena),
    };

    let object_decoder = match tag {
        None => {
            let mut with_payload = Vec::new();
            for case in &cases {
                let decoded = match &case.payload {
                    // serde also reads a unit variant written as a map.
                    CasePayload::Unit => {
                        let null_pat = json_pattern(arena, "Null", None);
                        let ok = ok_construct_none(case, arena);
                        let payload = ident(arena, "payload");
                        let error = spice_error(arena, "Expected null", payload);
                        let match_cases = vec![
                            super::case(null_pat, ok, arena),
                            super::case(pat_any(arena), error, arena),
                        ];
                        let payload = ident(arena, "payload");
                        expr_match(payload, match_cases, arena)
                    }
                    CasePayload::Args(args) => decode_args(settings, case, args, arena)?,
                    CasePayload::Record(fields) => {
                        let object_pat = {
                            let dict = pat_var_dummy(arena, "dict");
                            json_pattern(arena, "Object", Some(dict))
                        };
                        let record = records_generate_inline_decoder_expr(
                            settings,
                            fields,
                            case.constructor,
                            arena,
                        )?;
                        let payload = ident(arena, "payload");
                        let error = spice_error(arena, "Not an object", payload);
                        let match_cases = vec![
                            super::case(object_pat, record, arena),
                            super::case(pat_any(arena), error, arena),
                        ];
                        let payload = ident(arena, "payload");
                        expr_match(payload, match_cases, arena)
                    }
                };
                for name in std::iter::once(&case.name).chain(case.aliases.iter()) {
                    let prefix = format!(".{name}");
                    with_payload.push((name.clone(), with_path(&prefix, decoded.clone(), arena)));
                }
            }
            let otherwise = unknown_key(arena);
            let by_name = decode_by_name(with_payload, otherwise, arena);
            let entry_pat = {
                let spice_tag = pat_var_dummy(arena, "spice_tag");
                let payload = pat_var_dummy(arena, "payload");
                let entry = pat_tuple(vec![spice_tag, payload], arena);
                pat_array(vec![entry], arena)
            };
            let v = ident(arena, "v");
            let error = spice_error(arena, "Expected an object with one key", v);
            let match_cases = vec![
                super::case(entry_pat, by_name, arena),
                super::case(pat_any(arena), error, arena),
            ];
            let to_array = expr_ident_path(arena, &["Dict", "toArray"]);
            let dict = ident(arena, "dict");
            let entries = apply(arena, to_array, vec![dict]);
            expr_match(entries, match_cases, arena)
        }
        Some(tag) => {
            let mut records = Vec::new();
            for case in &cases {
                match &case.payload {
                    CasePayload::Unit => {}
                    CasePayload::Record(fields) => {
                        for name in std::iter::once(&case.name).chain(case.aliases.iter()) {
                            let decoded = records_generate_inline_decoder_expr(
                                settings,
                                fields,
                                case.constructor,
                                arena,
                            )?;
                            records.push((name.clone(), decoded));
                        }
                    }
                    CasePayload::Args(args) => {
                        // The payload decodes from the tagged object itself.
                        for name in std::iter::once(&case.name).chain(case.aliases.iter()) {
                            let untagged_fn = expr_ident_path(arena, &["Spice", "untagged"]);
                            let tag_expr = str_expr(arena, tag);
                            let dict = ident(arena, "dict");
                            let value = apply(arena, untagged_fn, vec![tag_expr, dict]);
                            let binding = ValueBinding {
                                pvb_jsx_component: None,
                                pvb_pat: {
                                    let pat = pat_var_dummy(arena, "payload");
                                    arena.push_pat(pat)
                                },
                                pvb_expr: arena.push_expr(value),
                                pvb_attributes: Attributes::new(),
                                pvb_loc: arena.dummy_loc(),
                            };
                            let body = decode_args(settings, case, args, arena)?;
                            records.push((
                                name.clone(),
                                expr_let(RecFlag::Nonrecursive, vec![binding], body, arena),
                            ));
                        }
                    }
                }
            }
            let mut by_names = units.clone();
            by_names.extend(records);
            let otherwise = invalid(arena);
            let by_name = decode_by_name(by_names, otherwise, arena);
            let some_pat = {
                let spice_tag = pat_var_dummy(arena, "spice_tag");
                let string = json_pattern(arena, "String", Some(spice_tag));
                pconstruct(arena, "Some", Some(string))
            };
            let missing = {
                let tag_expr = str_expr(arena, tag);
                let suffix = expr_constant_literal(arena, " missing");
                let message = expr_concat(arena, tag_expr, suffix);
                let v = ident(arena, "v");
                expr_spice_error_variants(arena, message, v, None)
            };
            let match_cases = vec![
                super::case(some_pat, by_name, arena),
                super::case(pat_any(arena), missing, arena),
            ];
            let get = expr_ident_path(arena, &["Dict", "get"]);
            let dict = ident(arena, "dict");
            let tag_expr = str_expr(arena, tag);
            let field = apply(arena, get, vec![dict, tag_expr]);
            expr_match(field, match_cases, arena)
        }
    };

    let mut match_cases = Vec::new();
    // First: JSON.Object alone would also match null here.
    {
        let null_pat = json_pattern(arena, "Null", None);
        let v = ident(arena, "v");
        let error = spice_error(arena, "Not a variant", v);
        match_cases.push(super::case(null_pat, error, arena));
    }
    if string_decodes {
        let string_pat = {
            let spice_tag = pat_var_dummy(arena, "spice_tag");
            json_pattern(arena, "String", Some(spice_tag))
        };
        let otherwise = invalid(arena);
        let by_name = decode_by_name(names, otherwise, arena);
        match_cases.push(super::case(string_pat, by_name, arena));
    }
    // Before JSON.Object, which also matches arrays at runtime.
    match legacy {
        Some(legacy) => {
            let empty_pat = {
                let empty = pat_array(vec![], arena);
                json_pattern(arena, "Array", Some(empty))
            };
            let v = ident(arena, "v");
            let error = spice_error(arena, "Expected variant, found empty array", v);
            match_cases.push(super::case(empty_pat, error, arena));
            let array_pat = {
                let json_arr = pat_var_dummy(arena, "json_arr");
                json_pattern(arena, "Array", Some(json_arr))
            };
            match_cases.push(super::case(array_pat, legacy, arena));
        }
        None => {
            let array_pat = {
                let any = pat_any(arena);
                json_pattern(arena, "Array", Some(any))
            };
            let v = ident(arena, "v");
            let error = spice_error(arena, "Expected variant, found array", v);
            match_cases.push(super::case(array_pat, error, arena));
        }
    }
    {
        let object_pat = {
            let dict = pat_var_dummy(arena, "dict");
            json_pattern(arena, "Object", Some(dict))
        };
        match_cases.push(super::case(object_pat, object_decoder, arena));
    }
    {
        let v = ident(arena, "v");
        let error = spice_error(arena, "Not a variant", v);
        match_cases.push(super::case(pat_any(arena), error, arena));
    }
    let scrutinee = json_typed(arena, "v");
    let mut decoded = expr_match(scrutinee, match_cases, arena);
    if !untagged.is_empty() {
        let ok_pat = {
            let any = pat_any(arena);
            let ok = pconstruct(arena, "Ok", Some(any));
            pat_alias(ok, "ok", arena)
        };
        let ok_rhs = ident(arena, "ok");
        let error_pat = {
            let any = pat_any(arena);
            let error = pconstruct(arena, "Error", Some(any));
            pat_alias(error, "error", arena)
        };
        let error = ident(arena, "error");
        let error_rhs = decode_untagged(settings, &untagged, error, arena)?;
        let cases = vec![
            super::case(ok_pat, ok_rhs, arena),
            super::case(error_pat, error_rhs, arena),
        ];
        decoded = expr_match(decoded, cases, arena);
    }
    Ok(expr_fun(
        ArgLabel::Nolabel,
        pat_var_dummy(arena, "v"),
        decoded,
        Some(1),
        arena,
    ))
}

/// serde.ml `generate_codecs`; `legacy` builds the default spice encoding's
/// decoder (given `json_arr`), used with `@spice.serde({legacy: true})`.
pub(super) fn generate_codecs(
    settings: GeneratorSettings,
    serde: Serde,
    tag: Option<StrIdx>,
    legacy: impl FnOnce(&mut ParseArena) -> SpiceResult<Expression>,
    cases: &[SerdeCase],
    arena: &mut ParseArena,
) -> SpiceResult<(Option<Expression>, Option<Expression>)> {
    let tag = tag.map(|tag| arena.get_string(tag).to_string());
    let tag = tag.as_deref();
    validate(tag, cases, arena)?;
    let encoder = if settings.do_encode {
        Some(generate_encoder(settings, tag, cases, arena)?)
    } else {
        None
    };
    let decoder = if settings.do_decode {
        let legacy = if serde.legacy {
            Some(legacy(arena)?)
        } else {
            None
        };
        Some(generate_decoder(settings, tag, legacy, cases, arena)?)
    } else {
        None
    };
    Ok((encoder, decoder))
}

// ---------------------------------------------------------------------------
// Variants (variants.ml) and polymorphic variants (polyvariants.ml)
// ---------------------------------------------------------------------------

/// variants.ml `serde_case`.
pub(super) fn variant_case(
    decl: &ParsedVariantDecl,
    arena: &mut ParseArena,
) -> SpiceResult<SerdeCase> {
    let constr = &decl.constr_decl;
    let (payload, lhs) = match &constr.pcd_args {
        crate::parser::ast::ConstructorArguments::Pcstr_tuple(args) if args.is_empty() => {
            let lid = arena.push_lident_from_idx(decl.name);
            (CasePayload::Unit, pat_construct(lid, None, arena))
        }
        crate::parser::ast::ConstructorArguments::Pcstr_tuple(args) => {
            let args: Vec<CoreType> = args
                .iter()
                .map(|idx| arena.get_core_type(*idx).clone())
                .collect();
            let pattern = args_pattern(args.len(), arena);
            let lid = arena.push_lident_from_idx(decl.name);
            (CasePayload::Args(args), pat_construct(lid, pattern, arena))
        }
        crate::parser::ast::ConstructorArguments::Pcstr_record(fields) => {
            let loc = arena.clone_loc(constr.pcd_loc);
            let pattern = variants_inline_record_payload_pattern(fields, loc, arena);
            let lid = arena.push_lident_from_idx(decl.name);
            (
                CasePayload::Record(fields.clone()),
                pat_construct(lid, Some(pattern), arena),
            )
        }
    };
    let (aliases, other, untagged) = flags_of_attributes(&constr.pcd_attributes, arena)?;
    Ok(SerdeCase {
        name: name_of_variant(decl, arena)?,
        constructor: decl.name,
        aliases,
        other,
        untagged,
        payload,
        lhs,
        construct: Construct::Variant(decl.name),
    })
}

/// polyvariants.ml `serde_case`.
pub(super) fn polyvariant_case(
    field: &ParsedPolyvariantField,
    arena: &mut ParseArena,
) -> SpiceResult<SerdeCase> {
    let RowField::Rtag(_, attrs, _, core_types) = &field.row_field else {
        return Err("This syntax is not yet implemented by spice".to_string());
    };
    let (aliases, other, untagged) = flags_of_attributes(attrs, arena)?;
    let args = polyvars_get_args(arena.dummy_loc(), core_types, arena)?;
    let pattern = args_pattern(args.len(), arena);
    let lhs = pat_variant(field.name.clone(), pattern, arena);
    let constructor = arena.intern_string(&field.name);
    Ok(SerdeCase {
        name: name_of_alias(field.has_attr_as, &field.alias, &field.name, arena)?,
        constructor,
        aliases,
        other,
        untagged,
        payload: if args.is_empty() {
            CasePayload::Unit
        } else {
            CasePayload::Args(args)
        },
        lhs,
        construct: Construct::Poly(field.name.clone()),
    })
}

/// `Array.getUnsafe json_arr 0`.
fn json_arr_head(arena: &mut ParseArena) -> Expression {
    let get = expr_ident_path(arena, &["Array", "getUnsafe"]);
    let json_arr = ident(arena, "json_arr");
    let zero = expr_constant(Constant::Integer(arena.intern_string(&"0"), None), arena);
    apply(arena, get, vec![json_arr, zero])
}

/// The `@spice.other` default of a legacy decoder.
fn legacy_other_default(message: &str, value: Expression, arena: &mut ParseArena) -> Expression {
    let length = {
        let func = expr_ident_path(arena, &["Array", "length"]);
        let json_arr = ident(arena, "json_arr");
        apply(arena, func, vec![json_arr])
    };
    let one = int_expr(arena, 1);
    let cond = expr_not_equal(arena, length, one);
    let v = ident(arena, "v");
    let error = spice_error(arena, message, v);
    let ok = construct(arena, "Ok", Some(value));
    expr_ifthenelse(cond, error, Some(ok), arena)
}

/// The cases for the `@spice.alias` names of a constructor: the
/// constructor's own legacy case under another name.
fn alias_cases(
    case: &Case,
    aliases: &[String],
    constructors: &[String],
    arena: &mut ParseArena,
) -> Vec<Case> {
    aliases
        .iter()
        .filter(|alias| !constructors.contains(alias))
        .map(|alias| {
            let pattern = Pattern {
                ppat_desc: PatternDesc::Ppat_constant(arena.string_constant(alias)),
                ppat_loc: arena.dummy_loc(),
                ppat_attributes: Attributes::new(),
            };
            // `Pat.construct (lid "JSON.String")`: the name has no location.
            let lhs = {
                let lid = lident_path_static(arena, &["JSON", "String"]);
                let loc = arena.none_loc();
                pat_construct_with_loc(lid, Some(pattern), loc, arena)
            };
            Case {
                pc_bar: None,
                pc_lhs: arena.push_pat(lhs),
                pc_guard: case.pc_guard,
                pc_rhs: case.pc_rhs,
            }
        })
        .collect()
}

/// variants.ml `generate_legacy_decoder`.
pub(super) fn variants_legacy_decoder(
    settings: GeneratorSettings,
    parsed: &[ParsedVariantDecl],
    arena: &mut ParseArena,
) -> SpiceResult<Expression> {
    let constructors: Vec<String> = parsed
        .iter()
        .map(|decl| arena.get_string(decl.name).to_string())
        .collect();
    let mut cases = Vec::new();
    let mut other = None;
    for decl in parsed {
        let case = variants_generate_decoder_case(settings, decl, arena)?;
        let (aliases, is_other, _) = flags_of_attributes(&decl.constr_decl.pcd_attributes, arena)?;
        if is_other && other.is_none() {
            other = Some(decl.name);
        }
        let aliases = alias_cases(&case, &aliases, &constructors, arena);
        cases.push(case);
        cases.extend(aliases);
    }
    let default = match other {
        Some(name) => {
            let lid = arena.push_lident_from_idx(name);
            let value = expr_construct(lid, None, arena);
            legacy_other_default(
                "Invalid number of arguments to variant constructor",
                value,
                arena,
            )
        }
        None => {
            let head = json_arr_head(arena);
            spice_error(arena, "Invalid variant constructor", head)
        }
    };
    cases.push(super::case(pat_any(arena), default, arena));
    let head = json_arr_head(arena);
    Ok(expr_match(head, cases, arena))
}

/// polyvariants.ml `generate_legacy_decoder`.
pub(super) fn polyvariants_legacy_decoder(
    settings: GeneratorSettings,
    parsed: &[ParsedPolyvariantField],
    arena: &mut ParseArena,
) -> SpiceResult<Expression> {
    let constructors: Vec<String> = parsed.iter().map(|row| row.name.to_string()).collect();
    let mut cases = Vec::new();
    let mut other = None;
    for row in parsed {
        let case = polyvars_generate_decoder_case(settings, &row.row_field, arena)?;
        let RowField::Rtag(_, attrs, _, _) = &row.row_field else {
            return Err("This syntax is not yet implemented by spice".to_string());
        };
        let (aliases, is_other, _) = flags_of_attributes(attrs, arena)?;
        if is_other && other.is_none() {
            other = Some(row.name.clone());
        }
        let aliases = alias_cases(&case, &aliases, &constructors, arena);
        cases.push(case);
        cases.extend(aliases);
    }
    let default = match other {
        Some(name) => {
            let value = expr_variant(name, None, arena);
            legacy_other_default(
                "Invalid number of arguments to polyvariant constructor",
                value,
                arena,
            )
        }
        None => {
            let head = json_arr_head(arena);
            let message = expr_constant_literal(arena, "Invalid polymorphic variant constructor");
            expr_spice_error_polyvars(arena, message, head, None)
        }
    };
    cases.push(super::case(pat_any(arena), default, arena));
    let head = json_arr_head(arena);
    Ok(expr_match(head, cases, arena))
}
