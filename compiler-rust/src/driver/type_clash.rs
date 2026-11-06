//! `Typecore.print_expr_type_clash` (compiler/ml/typecore.ml:762-820) with
//! the `Error_message_utils` helpers it uses
//! (compiler/ml/error_message_utils.ml), laid out through Format like
//! OCaml's `Location.errorf` messages.

use crate::parse_arena::{LocIdx, ParseArena};
use crate::parser::formatter::{BoxKind, Formatter};
use crate::types::asttypes::ArgLabel;
use crate::types::path::Path;
use crate::types::predef;
use crate::types::printtyp::{Printtyp, TAG_ERROR, TAG_INFO, TAG_RESET, TracePair, expand_trace};
use crate::types::type_expr::{TypeDesc, TypeExprRef};
use crate::types::typecore::JsxPropKind;
use crate::types::{Env, TypeClashContext, TypeContext};

type Ppf<'b> = Formatter<&'b mut Vec<u8>>;

fn open_tag(ppf: &mut Ppf<'_>, tag: &str) {
    ppf.string_as(0, tag);
}

fn close_tag(ppf: &mut Ppf<'_>) {
    ppf.string_as(0, TAG_RESET);
}

fn tagged(ppf: &mut Ppf<'_>, tag: &str, text: &str) {
    open_tag(ppf, tag);
    ppf.str(text);
    close_tag(ppf);
}

/// Literal text that may contain newlines: Format prints them raw, like the
/// `\n` escapes in OCaml's format strings.
fn raw(ppf: &mut Ppf<'_>, text: &str) {
    ppf.str(text);
}

/// `Location.errorf "%a@?"`: the message is formatted after a phantom
/// two-column prefix (location.ml:198-206) and printed after two spaces.
pub(super) fn render_error_message(f: impl FnOnce(&mut Ppf<'_>)) -> String {
    let mut buf = Vec::new();
    {
        let mut ppf = Formatter::new(&mut buf);
        ppf.string_as(2, "");
        f(&mut ppf);
        ppf.flush();
    }
    let mut message = String::from("  ");
    message.push_str(&String::from_utf8_lossy(&buf));
    message
}

/// Render Format output that starts at column 0 with no enclosing box, as
/// after a `@.` in an error message.
pub(super) fn render_error_message_at_column0(f: impl FnOnce(&mut Ppf<'_>)) -> String {
    let mut buf = Vec::new();
    {
        let mut ppf = Formatter::new(&mut buf);
        f(&mut ppf);
        ppf.flush();
    }
    String::from_utf8_lossy(&buf).into_owned()
}

/// `bottom_aliases` (typecore.ml:700-705).
fn bottom_aliases(tr: &[TracePair]) -> Option<(TypeExprRef, TypeExprRef)> {
    match tr {
        [(_, one), (_, two), rest @ ..] => bottom_aliases(rest).or(Some((*one, *two))),
        _ => None,
    }
}

/// `collect_missing_arguments env type1 type2` (typecore.ml:750-760). The
/// pattern matches read `desc` without `repr`, like OCaml.
fn collect_missing_arguments(
    ctx: &TypeContext,
    env: &Env,
    type1: TypeExprRef,
    type2: TypeExprRef,
) -> Option<Vec<(ArgLabel, TypeExprRef)>> {
    let (params, ret) = match &*ctx.borrow_desc(type1) {
        TypeDesc::Tarrow { args, ret } => (
            args.iter()
                .map(|a| (a.label().clone(), a.typ))
                .collect::<Vec<_>>(),
            *ret,
        ),
        _ => return None,
    };
    if crate::types::ctype::matches(ctx, env, ret, type2) {
        return Some(params);
    }
    let mut res = collect_missing_arguments(ctx, env, ret, type2)?;
    let mut all = params;
    all.append(&mut res);
    Some(all)
}

fn print_arguments(
    ppf: &mut Ppf<'_>,
    printer: &mut Printtyp<'_>,
    args: &[(ArgLabel, TypeExprRef)],
) {
    for (i, (label, argtype)) in args.iter().enumerate() {
        if i > 0 {
            ppf.str(",");
            ppf.space();
        }
        ppf.open_box(BoxKind::Box, 0);
        match label {
            ArgLabel::Nolabel => printer.pp_type_expr(ppf, *argtype),
            ArgLabel::Labelled(l) => {
                ppf.print(format_args!("(~{}: ", l.txt));
                printer.pp_type_expr(ppf, *argtype);
                ppf.str(")");
            }
            ArgLabel::Optional(l) => {
                ppf.print(format_args!("(?{}: ", l.txt));
                printer.pp_type_expr(ppf, *argtype);
                ppf.str(")");
            }
        }
        ppf.close_box();
    }
}

/// `error_type_text` (error_message_utils.ml:119-131).
fn error_type_text(ppf: &mut Ppf<'_>, context: &Option<TypeClashContext>) {
    let text = match context {
        Some(TypeClashContext::StatementFunctionCall) => "This function call returns:",
        Some(TypeClashContext::MathOperator {
            is_constant: Some(_),
            ..
        }) => "This value has type:",
        Some(TypeClashContext::ArrayLiteral) => "This array item has type:",
        Some(TypeClashContext::TaggedTemplateValue) => "This interpolated value has type:",
        Some(TypeClashContext::SetRecordField { .. }) => {
            "You're assigning something to this field that has type:"
        }
        Some(TypeClashContext::JsxComponent) => "This JSX tag has type:",
        _ => "This has type:",
    };
    ppf.str(text);
}

/// `error_expected_type_text` (error_message_utils.ml:133-193).
fn error_expected_type_text(ppf: &mut Ppf<'_>, context: &Option<TypeClashContext>) {
    match context {
        Some(TypeClashContext::FunctionArgument { optional, name }) => {
            ppf.print(format_args!(
                "But this{} function argument",
                if *optional { " optional" } else { "" }
            ));
            if let Some(name) = name {
                ppf.str(" ");
                tagged(ppf, TAG_INFO, &format!("~{name}"));
            }
            ppf.str(" is expecting:");
        }
        Some(TypeClashContext::JsxComponent) => ppf.str("But JSX component positions require:"),
        Some(TypeClashContext::ComparisonOperator) => {
            ppf.str("But it's being compared to something of type:")
        }
        Some(TypeClashContext::SwitchExpression) => {
            ppf.str("But this switch is expected to return:")
        }
        Some(TypeClashContext::LetUnwrapReturn) => {
            ppf.str("But this ");
            tagged(ppf, TAG_INFO, "let?");
            ppf.str(" is used where this type is expected:");
        }
        Some(TypeClashContext::TryReturn) => ppf.str("But this try/catch is expected to return:"),
        Some(TypeClashContext::WhileCondition) => {
            ppf.str("But a ");
            tagged(ppf, TAG_INFO, "while");
            ppf.str(" loop condition must always be of type:");
        }
        Some(TypeClashContext::ForLoopCondition) => {
            ppf.str("But a ");
            tagged(ppf, TAG_INFO, "for");
            ppf.str(" loop bounds must always be of type:");
        }
        Some(TypeClashContext::IfCondition) => {
            ppf.str("But ");
            tagged(ppf, TAG_INFO, "if");
            ppf.str(" conditions must always be of type:");
        }
        Some(TypeClashContext::AssertCondition) => {
            ppf.str("But assertions must always be of type:")
        }
        Some(TypeClashContext::IfReturn) => {
            ppf.str("But this ");
            tagged(ppf, TAG_INFO, "if");
            ppf.str(" statement is expected to return:");
        }
        Some(TypeClashContext::TernaryReturn) => ppf.str("But this ternary is expected to return:"),
        Some(TypeClashContext::ArrayLiteral) => {
            ppf.str("But this array is expected to have items of type:")
        }
        Some(TypeClashContext::TaggedTemplateValue) => {
            ppf.str("But this tag expects interpolations of type:")
        }
        Some(TypeClashContext::SetRecordField { .. }) => {
            ppf.str("But the record field is of type:")
        }
        Some(TypeClashContext::RecordField {
            field_name,
            jsx: Some(JsxPropKind::Fragment),
            ..
        }) if field_name == "children" => ppf.str("But children of JSX fragments must be of type:"),
        Some(TypeClashContext::RecordField {
            field_name,
            jsx: Some(JsxPropKind::CustomComponent),
            ..
        }) if field_name == "children" => {
            ppf.str("But children passed to this component must be of type:")
        }
        Some(TypeClashContext::RecordField {
            field_name,
            jsx: Some(_),
            ..
        }) => {
            ppf.str("But the component prop ");
            tagged(ppf, TAG_INFO, field_name);
            ppf.str(" is expected to have type:");
        }
        Some(TypeClashContext::RecordField { field_name, .. }) => {
            ppf.str("But the record field ");
            tagged(ppf, TAG_INFO, field_name);
            ppf.str(" is expected to have type:");
        }
        Some(TypeClashContext::StatementFunctionCall) => ppf.str("But it's expected to return:"),
        Some(TypeClashContext::MathOperator { operator, .. }) => {
            ppf.str("But it's being used with the ");
            tagged(ppf, TAG_INFO, operator);
            ppf.str(" operator, which works on:");
        }
        Some(TypeClashContext::StringConcat) => ppf.str("But string concatenation is expecting:"),
        Some(TypeClashContext::Await) => {
            ppf.str("But you're using ");
            tagged(ppf, TAG_INFO, "await");
            ppf.str(" on this expression, so it is expected to be of type:");
        }
        _ => ppf.str("But it's expected to have type:"),
    }
}

/// The source of `loc` (`Parser.extract_text_at_loc`).
fn extract_text_at_loc(arena: &ParseArena, source: &str, loc: LocIdx) -> String {
    let start = arena.loc_start(loc).cnum as usize;
    let end = arena.loc_end(loc).cnum as usize;
    crate::source_text::latin1_slice(source, start, end)
        .unwrap_or("")
        .to_string()
}

/// `!Parser.parse_source` then `!Parser.reprint_source`, applied to the
/// expression at `loc` after `mapper` (`Parser.reprint_expr_at_loc`).
fn reprint_expr_at_loc(
    ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
    mapper: impl FnOnce(
        &mut ParseArena,
        crate::parser::ast::Expression,
    ) -> Option<crate::parser::ast::Expression>,
) -> Option<String> {
    let text = extract_text_at_loc(arena, source, loc);
    let mut parser = crate::parser::Parser::new("<none>", &text);
    let structure = crate::parser::module::parse_structure(&mut parser);
    ctx.push_reparse_warnings(parser.warnings());
    let comments = parser.take_comments();
    let mut sub_arena = parser.into_arena();
    let [item] = structure.as_slice() else {
        return None;
    };
    let crate::parser::ast::StructureItemDesc::Pstr_eval(eval) = &item.pstr_desc else {
        return None;
    };
    let exp = sub_arena.get_expr(eval.0).clone();
    let exp = mapper(&mut sub_arena, exp)?;
    let exp_idx = sub_arena.push_expr(exp);
    let wrapped = crate::parser::ast::StructureItem {
        pstr_desc: crate::parser::ast::StructureItemDesc::Pstr_eval(Box::new((
            exp_idx,
            crate::parser::ast::Attributes::new(),
        ))),
        pstr_loc: LocIdx::none(),
    };
    let printed =
        crate::parser::printer::print_implementation(&[wrapped], comments, 80, &mut sub_arena);
    Some(printed.trim().to_string())
}

/// `!Parser.parse_source text` followed by `!Parser.reprint_source`.
fn parse_and_reprint(ctx: &TypeContext, text: &str) -> Option<String> {
    let mut parser = crate::parser::Parser::new("<none>", text);
    let structure = crate::parser::module::parse_structure(&mut parser);
    ctx.push_reparse_warnings(parser.warnings());
    if structure.is_empty() {
        return None;
    }
    let comments = parser.take_comments();
    let mut sub_arena = parser.into_arena();
    Some(crate::parser::printer::print_implementation(
        &structure,
        comments,
        80,
        &mut sub_arena,
    ))
}

/// Whether `text` parses to a single constant expression.
fn text_is_constant(ctx: &TypeContext, text: &str) -> bool {
    let mut parser = crate::parser::Parser::new("<none>", text);
    let structure = crate::parser::module::parse_structure(&mut parser);
    ctx.push_reparse_warnings(parser.warnings());
    let arena = parser.into_arena();
    match structure.as_slice() {
        [item] => match &item.pstr_desc {
            crate::parser::ast::StructureItemDesc::Pstr_eval(eval) => matches!(
                &arena.get_expr(eval.0).pexp_desc,
                crate::parser::ast::ExpressionDesc::Pexp_constant(_)
            ),
            _ => false,
        },
        _ => false,
    }
}

/// `extract_string_constant`.
fn extract_string_constant(ctx: &TypeContext, text: &str) -> Option<String> {
    let mut parser = crate::parser::Parser::new("<none>", text);
    let structure = crate::parser::module::parse_structure(&mut parser);
    ctx.push_reparse_warnings(parser.warnings());
    let arena = parser.into_arena();
    let [item] = structure.as_slice() else {
        return None;
    };
    let crate::parser::ast::StructureItemDesc::Pstr_eval(eval) = &item.pstr_desc else {
        return None;
    };
    match &arena.get_expr(eval.0).pexp_desc {
        crate::parser::ast::ExpressionDesc::Pexp_constant(c) => match &*c {
            crate::parser::ast::Constant::String(payload) => {
                Some(payload.semantic(&arena).to_string())
            }
            _ => None,
        },
        _ => None,
    }
}

/// `Typecore.extract_concrete_typedecl`.
fn extract_concrete_typedecl(
    ctx: &TypeContext,
    env: &Env,
    ty: TypeExprRef,
) -> Option<crate::types::TypeDeclaration> {
    let mut current = ctx.repr(ty);
    loop {
        let path = match &*ctx.borrow_desc(current) {
            TypeDesc::Tconstr { path, .. } => path.clone(),
            _ => return None,
        };
        let decl = crate::types::typemod::find_type_decl_for_path(env, ctx, &path)?;
        if !matches!(decl.type_kind, crate::types::decl::TypeKind::TypeAbstract) {
            return Some(decl);
        }
        current = ctx.repr(crate::types::ctype::expand_head_once(ctx, env, current)?);
    }
}

fn head_path(ctx: &TypeContext, ty: TypeExprRef) -> Option<Path> {
    match &*ctx.borrow_desc(ty) {
        TypeDesc::Tconstr { path, .. } => Some(path.clone()),
        _ => None,
    }
}

fn is_jsx_path(path: &Path, name: &str) -> bool {
    matches!(path, Path::Pdot(parent, s, _)
        if s == name && matches!(parent.as_ref(), Path::Pident(id) if id.name() == "Jsx"))
}

fn expands_to_jsx(ctx: &TypeContext, env: &Env, ty: TypeExprRef, name: &str) -> bool {
    let e = crate::types::ctype::expand_head(ctx, env, ty);
    head_path(ctx, e).is_some_and(|p| is_jsx_path(&p, name))
}

const JSX_MODULE: &str = "React";

fn with_configured_jsx_module(s: &str) -> String {
    format!("{JSX_MODULE}.{s}")
}

/// `print_extra_type_clash_help` (error_message_utils.ml:236-798).
#[allow(clippy::too_many_arguments)]
fn print_extra_type_clash_help(
    ppf: &mut Ppf<'_>,
    printer: &mut Printtyp<'_>,
    ctx: &TypeContext,
    env: &Env,
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
    bottom: Option<(TypeExprRef, TypeExprRef)>,
    trace: &[TracePair],
    context: &Option<TypeClashContext>,
) {
    let desc = |t: TypeExprRef| (*ctx.get_desc(t)).clone();
    let bottom_paths = bottom.map(|(a, e)| (head_path(ctx, a), head_path(ctx, e)));
    match context {
        Some(TypeClashContext::MathOperator {
            for_float,
            operator,
            is_constant,
        }) => {
            let operator_for_other_type = match operator.as_str() {
                "+" => "+.",
                "+." => "+",
                "/" => "/.",
                "/." => "/",
                "-" => "-.",
                "*" => "*.",
                "*." => "*",
                v => v,
            };
            let operator_text = match operator.as_bytes().first() {
                Some(b'+') => "add",
                Some(b'-') => "subtract",
                Some(b'/') => "divide",
                Some(b'*') => "multiply",
                _ => "compute",
            };
            let string_path = predef::path_string();
            match (operator.as_str(), &bottom_paths) {
                ("+", Some((Some(p1), Some(p2))))
                    if string_path.same(p1) || string_path.same(p2) =>
                {
                    raw(
                        ppf,
                        "\n\n  Are you looking to concatenate strings? Use the operator ",
                    );
                    tagged(ppf, TAG_INFO, "++");
                    raw(
                        ppf,
                        ", which concatenates strings.\n\n  Possible solutions:\n  - Change the ",
                    );
                    tagged(ppf, TAG_INFO, "+");
                    raw(ppf, " operator to ");
                    tagged(ppf, TAG_INFO, "++");
                    raw(ppf, " to concatenate strings instead.");
                }
                _ => {
                    raw(
                        ppf,
                        &format!(
                            "\n\n  Floats and ints have their own mathematical operators. This means you cannot {operator_text} a float and an int without converting between the two.\n\n  Possible solutions:\n  - Ensure all values in this calculation have the type "
                        ),
                    );
                    tagged(ppf, TAG_INFO, if *for_float { "float" } else { "int" });
                    raw(ppf, ". You can convert between floats and ints via ");
                    tagged(ppf, TAG_INFO, "Float.toInt");
                    raw(ppf, " and ");
                    tagged(ppf, TAG_INFO, "Int.fromFloat");
                    raw(ppf, ".");
                }
            }
            match (is_constant, &bottom_paths) {
                (Some(constant), _) => {
                    if *for_float {
                        raw(ppf, "\n  - Make ");
                        tagged(ppf, TAG_INFO, constant);
                        raw(ppf, " a ");
                        tagged(ppf, TAG_INFO, "float");
                        raw(ppf, " by adding a trailing dot: ");
                        tagged(ppf, TAG_INFO, &format!("{constant}."));
                    } else {
                        raw(ppf, "\n  - Make ");
                        tagged(ppf, TAG_INFO, constant);
                        raw(ppf, " an ");
                        tagged(ppf, TAG_INFO, "int");
                        raw(ppf, " by removing the dot or explicitly converting to int");
                    }
                }
                (None, Some((Some(p1), Some(p2)))) => {
                    match (p1.name().as_str(), p2.name().as_str()) {
                        ("float", "int") | ("int", "float") => {
                            raw(ppf, "\n  - Change the operator to ");
                            tagged(ppf, TAG_INFO, operator_for_other_type);
                            raw(ppf, ", which works on ");
                            tagged(ppf, TAG_INFO, if *for_float { "int" } else { "float" });
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        Some(TypeClashContext::SwitchExpression) => {
            raw(ppf, "\n\n  All branches in a ");
            tagged(ppf, TAG_INFO, "switch");
            raw(ppf, " must return the same type.");
            ppf.cut();
            raw(
                ppf,
                "To fix this, change your branch to return the expected type.",
            );
        }
        Some(TypeClashContext::LetUnwrapReturn) => {
            let option = predef::path_option();
            let result = predef::path_result();
            let is = |p: &Option<Path>, target: &Path| p.as_ref().is_some_and(|p| p.same(target));
            let kind = match &bottom_paths {
                Some((a, _)) if is(a, &option) => 1,
                Some((_, e)) if is(e, &option) => 1,
                Some((a, _)) if is(a, &result) => 2,
                Some((_, e)) if is(e, &result) => 2,
                _ => 0,
            };
            print_let_unwrap_help(ppf, kind);
        }
        Some(TypeClashContext::TryReturn) => {
            raw(ppf, "\n\n  The ");
            tagged(ppf, TAG_INFO, "try");
            raw(ppf, " body and the ");
            tagged(ppf, TAG_INFO, "catch");
            raw(ppf, " block must return the same type.");
            ppf.cut();
            raw(
                ppf,
                "To fix this, change your try/catch blocks to return the expected type.",
            );
        }
        Some(TypeClashContext::IfCondition) => {
            raw(
                ppf,
                "\n\n  To fix this, change the highlighted code so it evaluates to a ",
            );
            tagged(ppf, TAG_INFO, "bool");
            raw(ppf, ".");
        }
        Some(TypeClashContext::Await) => {
            raw(
                ppf,
                "\n\n  You're trying to await something that is not a promise.\n\nPossible solutions:\n  - Remove the ",
            );
            tagged(ppf, TAG_INFO, "await");
            raw(
                ppf,
                " if this is not expected to be a promise\n  - Wrap the expression in ",
            );
            tagged(ppf, TAG_INFO, "Promise.resolve");
            raw(ppf, " to convert the expression to a promise");
        }
        Some(TypeClashContext::JsxComponent) => {
            raw(
                ppf,
                "\n\n  JSX tags must be React components, not plain functions.\n\n  Possible solutions:\n  - If this function takes labeled props, annotate it with ",
            );
            tagged(ppf, TAG_INFO, "@react.component");
            raw(
                ppf,
                "\n  - If this function takes a single props record, annotate it with ",
            );
            tagged(ppf, TAG_INFO, "@react.componentWithProps");
            raw(
                ppf,
                "\n  - If this is already a valid component-like value, wrap it with ",
            );
            tagged(ppf, TAG_INFO, "React.component(...)");
        }
        Some(TypeClashContext::IfReturn) => {
            raw(ppf, "\n\n  ");
            tagged(ppf, TAG_INFO, "if");
            raw(
                ppf,
                " expressions must return the same type in all branches (",
            );
            tagged(ppf, TAG_INFO, "if");
            raw(ppf, ", ");
            tagged(ppf, TAG_INFO, "else if");
            raw(ppf, ", ");
            tagged(ppf, TAG_INFO, "else");
            raw(ppf, ").");
        }
        Some(TypeClashContext::TernaryReturn) => {
            raw(ppf, "\n\n  Ternaries (");
            tagged(ppf, TAG_INFO, "?");
            raw(ppf, " and ");
            tagged(ppf, TAG_INFO, ":");
            raw(ppf, ") must return the same type in both branches.");
        }
        Some(TypeClashContext::ComparisonOperator) => {
            raw(ppf, "\n\n  You can only compare things of the same type.");
        }
        // | Some ArrayValue, Some ({desc = Tobject _}, ({desc = Tconstr _} as t1))
        //   when is_record_type t1 -> print_object_vs_record_hint
        Some(TypeClashContext::ArrayLiteral)
            if bottom.is_some_and(|(b1, b2)| {
                matches!(desc(b1), TypeDesc::Tobject { .. })
                    && head_path(ctx, b2).is_some()
                    && is_record_type(ctx, env, b2)
            }) =>
        {
            print_object_vs_record_hint(ppf, ctx, arena, source, loc);
        }
        Some(TypeClashContext::ArrayLiteral) => {
            raw(
                ppf,
                "\n\n  Arrays can only contain items of the same type.\n\n  Possible solutions:\n  - Convert all values in the array to the same type.\n  - Use a tuple, if your array is of fixed length. Tuples can mix types freely, and compiles to a JavaScript array. Example of a tuple: `let myTuple = (10, \"hello\", 15.5, true)",
            );
        }
        _ => print_extra_type_clash_help_by_types(
            ppf, printer, ctx, env, arena, source, loc, bottom, trace, context, &desc,
        ),
    }
}

fn print_let_unwrap_help(ppf: &mut Ppf<'_>, kind: u8) {
    match kind {
        1 => {
            raw(ppf, "\n\n  This ");
            tagged(ppf, TAG_INFO, "let?");
            raw(ppf, " unwraps an ");
            tagged(ppf, TAG_INFO, "option");
            raw(
                ppf,
                "; use it where the enclosing function or let binding returns an ",
            );
            tagged(ppf, TAG_INFO, "option");
            raw(ppf, " so ");
            tagged(ppf, TAG_INFO, "None");
            raw(
                ppf,
                " can propagate.\n\n  Possible solutions:\n  - Change the enclosing function or let binding to return ",
            );
            tagged(ppf, TAG_INFO, "option<'t>");
            raw(ppf, " and use ");
            tagged(ppf, TAG_INFO, "Some");
            raw(ppf, " for success; ");
            tagged(ppf, TAG_INFO, "let?");
            raw(ppf, " will propagate ");
            tagged(ppf, TAG_INFO, "None");
            raw(ppf, ".\n  - Replace ");
            tagged(ppf, TAG_INFO, "let?");
            raw(ppf, " with a ");
            tagged(ppf, TAG_INFO, "switch");
            raw(ppf, " and handle the ");
            tagged(ppf, TAG_INFO, "None");
            raw(
                ppf,
                " case explicitly.\n  - If you want a default value instead of early return, unwrap using ",
            );
            tagged(ppf, TAG_INFO, "Option.getOr(default)");
            raw(ppf, ".");
        }
        2 => {
            raw(ppf, "\n\n  This ");
            tagged(ppf, TAG_INFO, "let?");
            raw(ppf, " unwraps a ");
            tagged(ppf, TAG_INFO, "result");
            raw(
                ppf,
                "; use it where the enclosing function or let binding returns a ",
            );
            tagged(ppf, TAG_INFO, "result");
            raw(ppf, " so ");
            tagged(ppf, TAG_INFO, "Error");
            raw(
                ppf,
                " can propagate.\n\n  Possible solutions:\n  - Change the enclosing function or let binding to return ",
            );
            tagged(ppf, TAG_INFO, "result<'ok, 'error>");
            raw(ppf, "; use ");
            tagged(ppf, TAG_INFO, "Ok");
            raw(ppf, " for success, and ");
            tagged(ppf, TAG_INFO, "let?");
            raw(ppf, " will propagate ");
            tagged(ppf, TAG_INFO, "Error");
            raw(ppf, ".\n  - Replace ");
            tagged(ppf, TAG_INFO, "let?");
            raw(ppf, " with a ");
            tagged(ppf, TAG_INFO, "switch");
            raw(ppf, " and handle the ");
            tagged(ppf, TAG_INFO, "Error");
            raw(
                ppf,
                " case explicitly.\n  - If you want a default value instead of early return, unwrap using ",
            );
            tagged(ppf, TAG_INFO, "Result.getOr(default)");
            raw(ppf, ".");
        }
        _ => {
            raw(ppf, "\n\n  ");
            tagged(ppf, TAG_INFO, "let?");
            raw(ppf, " can only be used in a context that expects ");
            tagged(ppf, TAG_INFO, "option");
            raw(ppf, " or ");
            tagged(ppf, TAG_INFO, "result");
            raw(
                ppf,
                ".\n\n  Possible solutions:\n  - Change the enclosing function or let binding to return an ",
            );
            tagged(ppf, TAG_INFO, "option<'t>");
            raw(ppf, " or ");
            tagged(ppf, TAG_INFO, "result<'ok, 'error>");
            raw(ppf, " and propagate with ");
            tagged(ppf, TAG_INFO, "Some/Ok");
            raw(ppf, ".\n  - Replace ");
            tagged(ppf, TAG_INFO, "let?");
            raw(ppf, " with a ");
            tagged(ppf, TAG_INFO, "switch");
            raw(ppf, " and handle the ");
            tagged(ppf, TAG_INFO, "None/Error");
            raw(
                ppf,
                " case explicitly.\n  - If you want a default value instead of early return, unwrap using ",
            );
            tagged(ppf, TAG_INFO, "Option.getOr(default)");
            raw(ppf, " or ");
            tagged(ppf, TAG_INFO, "Result.getOr(default)");
            raw(ppf, ".");
        }
    }
}

fn is_record_type(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> bool {
    extract_concrete_typedecl(ctx, env, ty)
        .is_some_and(|d| matches!(d.type_kind, crate::types::decl::TypeKind::TypeRecord(..)))
}

/// error_message_utils.ml `print_object_vs_record_hint`.
fn print_object_vs_record_hint(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
) {
    ppf.cut();
    ppf.cut();
    ppf.str("You're passing a ");
    tagged(ppf, TAG_ERROR, "ReScript object");
    ppf.str(" where a ");
    tagged(ppf, TAG_INFO, "record");
    ppf.str(" is expected. Objects are written with quoted keys, and records with unquoted keys.");
    let suggested = reprint_expr_at_loc(ctx, arena, source, loc, |a, exp| {
        let crate::parser::ast::ExpressionDesc::Pexp_object_literal(fields) = &exp.pexp_desc else {
            return None;
        };
        let rows = fields
            .iter()
            .map(|(name, e)| {
                let name_idx = a.intern(&name.txt);
                let lid = a.push_longident(crate::parser::longident::Longident::Lident(name_idx));
                crate::parser::ast::ExpressionRecordField {
                    lid: crate::parser::ast::Loc {
                        txt: lid,
                        loc: name.loc,
                    },
                    expr: *e,
                    opt: false,
                }
            })
            .collect::<Vec<_>>();
        Some(crate::parser::ast::Expression {
            pexp_desc: crate::parser::ast::ExpressionDesc::Pexp_record((
                a.push_expr_field_list(&rows),
                None,
            )),
            pexp_loc: exp.pexp_loc,
            pexp_attributes: crate::parser::ast::Attributes::new(),
        })
    });
    ppf.cut();
    ppf.cut();
    ppf.str("Possible solutions: ");
    ppf.cut();
    ppf.str("- Rewrite the object to a record");
    if suggested.is_some() {
        ppf.str(", like: ");
    }
    tagged(ppf, TAG_INFO, suggested.as_deref().unwrap_or(""));
    ppf.cut();
}

fn is_variant_type(ctx: &TypeContext, env: &Env, ty: TypeExprRef) -> bool {
    extract_concrete_typedecl(ctx, env, ty)
        .is_some_and(|d| matches!(d.type_kind, crate::types::decl::TypeKind::TypeVariant(..)))
}

/// The type-directed branches of `print_extra_type_clash_help`, taken when
/// the context has no specific help (error_message_utils.ml:436-797).
#[allow(clippy::too_many_arguments)]
fn print_extra_type_clash_help_by_types(
    ppf: &mut Ppf<'_>,
    printer: &mut Printtyp<'_>,
    ctx: &TypeContext,
    env: &Env,
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
    bottom: Option<(TypeExprRef, TypeExprRef)>,
    trace: &[TracePair],
    context: &Option<TypeClashContext>,
    desc: &dyn Fn(TypeExprRef) -> TypeDesc,
) {
    let Some((b1, b2)) = bottom else {
        return;
    };
    let d1 = desc(b1);
    let d2 = desc(b2);
    let p1 = head_path(ctx, b1);
    let p2 = head_path(ctx, b2);
    let is = |p: &Option<Path>, target: Path| p.as_ref().is_some_and(|p| target.same(p));

    // | _, Some ({desc = Tarrow _}, expected) when is_jsx_component_type ~env expected
    if matches!(d1, TypeDesc::Tarrow { .. }) && expands_to_jsx(ctx, env, b2, "component") {
        raw(
            ppf,
            "\n\n  A React component is expected here, but this expression is a plain function.\n\n  Possible solutions:\n  - Extract it to a component annotated with ",
        );
        tagged(ppf, TAG_INFO, "@react.component");
        raw(ppf, " or ");
        tagged(ppf, TAG_INFO, "@react.componentWithProps");
        raw(
            ppf,
            "\n  - If this is already a valid component-like value, wrap it with ",
        );
        tagged(ppf, TAG_INFO, "React.component(...)");
        return;
    }
    // | _, Some (_, {desc = Tconstr (p2, _, _)}) when Path.same Predef.path_dict p2
    if is(&p2, predef::path_dict()) {
        ppf.cut();
        ppf.cut();
        ppf.str("Dicts are written like: ");
        tagged(ppf, TAG_INFO, "dict{\"a\": 1, \"b\": 2}");
        ppf.cut();
        return;
    }
    // | _, Some ({desc = Tconstr _} as ty, {desc = Tconstr (p2, _, _)}) when p2 = unit
    if p1.is_some() && is(&p2, predef::path_unit()) {
        raw(ppf, "\n\n");
        if expands_to_jsx(ctx, env, b1, "element") {
            raw(
                ppf,
                "  - Did you forget to wrap this + adjacent JSX in a JSX fragment (",
            );
            tagged(ppf, TAG_INFO, "<></>");
            raw(
                ppf,
                ")?\n  - Did you mean to assign this to a variable?\n\n",
            );
        } else {
            raw(
                ppf,
                "  - Did you mean to assign this to a variable?\n  - If you don't care about the result of this expression, you can assign it to ",
            );
            tagged(ppf, TAG_INFO, "_");
            raw(ppf, " via ");
            tagged(ppf, TAG_INFO, "let _ = ...");
            raw(ppf, " or pipe it to ");
            tagged(ppf, TAG_INFO, "ignore");
            raw(ppf, " via ");
            tagged(ppf, TAG_INFO, "expression->ignore");
            raw(ppf, "\n\n");
        }
        return;
    }
    // | _, Some ({desc = Tobject _}, ({desc = Tconstr _} as t1)) when is_record_type t1
    if matches!(d1, TypeDesc::Tobject { .. }) && p2.is_some() && is_record_type(ctx, env, b2) {
        print_object_vs_record_hint(ppf, ctx, arena, source, loc);
        return;
    }
    // | _, Some ({desc = Tconstr (p1, _, _)}, _) when p1 = promise
    if is(&p1, predef::path_promise()) {
        raw(
            ppf,
            "\n\n  - Did you mean to await this promise before using it?\n",
        );
        return;
    }
    // | _, Some ({desc = Tconstr (p1, _, _)}, {desc = Ttuple _}) when p1 = array
    if is(&p1, predef::path_array()) && matches!(d2, TypeDesc::Ttuple(_)) {
        let suggested = reprint_expr_at_loc(ctx, arena, source, loc, |_, exp| {
            let crate::parser::ast::ExpressionDesc::Pexp_array(items) = &exp.pexp_desc else {
                return None;
            };
            let items = items.clone();
            Some(crate::parser::ast::Expression {
                pexp_desc: crate::parser::ast::ExpressionDesc::Pexp_tuple(items),
                ..exp
            })
        });
        raw(
            ppf,
            "\n\n  - Fix this by passing a tuple instead of an array",
        );
        if suggested.is_some() {
            raw(ppf, ", like: ");
        }
        tagged(ppf, TAG_INFO, suggested.as_deref().unwrap_or(""));
        raw(ppf, "\n");
        return;
    }
    // | _, Some ({desc = Tconstr (p, type_params, _)}, {desc = Tconstr (Jsx.element)})
    if let (
        Some(p),
        TypeDesc::Tconstr {
            args: type_params, ..
        },
    ) = (&p1, &d1)
        && p2.as_ref().is_some_and(|p2| is_jsx_path(p2, "element"))
    {
        let print_jsx_msg = |ppf: &mut Ppf<'_>, name: &str, target_fn: &str, extra: &str| {
            ppf.cut();
            ppf.cut();
            ppf.print(format_args!(
                "In JSX, all content must be JSX elements. You can convert {name} to a JSX element with "
            ));
            tagged(ppf, TAG_INFO, target_fn);
            ppf.print(format_args!("{extra}."));
            ppf.cut();
        };
        if p.same(&predef::path_int()) {
            print_jsx_msg(ppf, "int", &with_configured_jsx_module("int"), "");
        } else if p.same(&predef::path_string()) {
            print_jsx_msg(ppf, "string", &with_configured_jsx_module("string"), "");
        } else if p.same(&predef::path_float()) {
            print_jsx_msg(ppf, "float", &with_configured_jsx_module("float"), "");
        } else if type_params.len() == 1 && p.same(&predef::path_option()) {
            ppf.cut();
            ppf.cut();
            ppf.str("You need to unwrap this option to its underlying value first, then turn that value into a JSX element.");
            ppf.cut();
            ppf.str("For ");
            tagged(ppf, TAG_INFO, "None");
            ppf.str(", you can use ");
            tagged(ppf, TAG_INFO, &with_configured_jsx_module("null"));
            ppf.str(" to output nothing into JSX.");
            ppf.cut();
        } else if type_params.len() == 1
            && p.same(&predef::path_array())
            && expands_to_jsx(ctx, env, type_params[0], "element")
        {
            let extra = format!(
                " (for example by using a pipe: ->{}.",
                with_configured_jsx_module("array")
            );
            print_jsx_msg(ppf, "array", &with_configured_jsx_module("array"), &extra);
        } else if type_params.len() == 1 && p.same(&predef::path_array()) {
            ppf.cut();
            ppf.cut();
            ppf.str(
                "You need to convert each item in this array to a JSX element first, then use ",
            );
            tagged(ppf, TAG_INFO, &with_configured_jsx_module("array"));
            ppf.str(" to convert the array of JSX elements into a single JSX element.");
            ppf.cut();
        }
        return;
    }
    let option_path = predef::path_option();
    // | Some (RecordField {optional = true; jsx = None}), Some ({desc = Tconstr (p)}, _) when p = option
    if let Some(TypeClashContext::RecordField {
        optional: true,
        field_name,
        jsx,
    }) = context
        && is(&p1, option_path.clone())
    {
        let text = extract_text_at_loc(arena, source, loc);
        let (what, example) = if jsx.is_none() {
            ("record field", format!("{{{field_name}: ?{text}"))
        } else {
            ("component prop", format!("{field_name}=?{text}"))
        };
        ppf.cut();
        ppf.cut();
        tagged(ppf, TAG_INFO, field_name);
        ppf.print(format_args!(
            " is an optional {what}, and you're passing an optional value to it."
        ));
        ppf.cut();
        ppf.print(format_args!(
            "Values passed to an optional {what} don't need to be wrapped in an option. You might need to adjust the type of the value supplied.\n       "
        ));
        ppf.cut();
        ppf.str("Possible solutions: ");
        ppf.cut();
        ppf.str("- Unwrap the option from the value you're passing in");
        ppf.cut();
        ppf.str("- If you really do want to pass the optional value, prepend the value with ");
        tagged(ppf, TAG_INFO, "?");
        ppf.str(" to show you want to pass the option, like: ");
        tagged(ppf, TAG_INFO, &example);
        if jsx.is_none() {
            ppf.str("}");
        }
        return;
    }
    // | Some (FunctionArgument {optional = true}), Some ({desc = Tconstr (p)}, _) when p = option
    if let Some(TypeClashContext::FunctionArgument { optional: true, .. }) = context
        && is(&p1, option_path)
    {
        let text = extract_text_at_loc(arena, source, loc);
        ppf.cut();
        ppf.cut();
        ppf.str("You're passing an optional value into an optional function argument.");
        ppf.cut();
        ppf.str("Values passed to an optional function argument don't need to be wrapped in an option. You might need to adjust the type of the value supplied.\n       ");
        ppf.cut();
        ppf.str("Possible solutions: ");
        ppf.cut();
        ppf.str("- Unwrap the option from the value you're passing in");
        ppf.cut();
        ppf.str("- If you really do want to pass the optional value, prepend the value with ");
        tagged(ppf, TAG_INFO, "?");
        ppf.str(" to show you want to pass the option, like: ");
        tagged(ppf, TAG_INFO, &format!("?{text}"));
        return;
    }
    // | Some BracedIdent, Some (_, ({desc = Tconstr _} as t)) when is_record_type t
    if matches!(context, Some(TypeClashContext::BracedIdent))
        && p2.is_some()
        && is_record_type(ctx, env, b2)
    {
        let rewrite = reprint_expr_at_loc(ctx, arena, source, loc, |a, exp| {
            let crate::parser::ast::ExpressionDesc::Pexp_ident(lid) = &exp.pexp_desc else {
                return None;
            };
            let lid_txt = lid.txt;
            let x = a.push_expr(exp.clone());
            let none_loc = a.none_loc();
            Some(crate::parser::ast::Expression {
                pexp_desc: crate::parser::ast::ExpressionDesc::Pexp_record((
                    a.push_expr_field_list(&[crate::parser::ast::ExpressionRecordField {
                        lid: crate::parser::ast::Loc {
                            txt: lid_txt,
                            loc: none_loc,
                        },
                        expr: x,
                        opt: false,
                    }]),
                    None,
                )),
                ..exp
            })
        });
        ppf.cut();
        ppf.cut();
        ppf.str("You might have meant to pass this as a record, but wrote it as a block.");
        ppf.cut();
        ppf.str("Braces with a single identifier counts as a block, not a record with a single (punned) field.");
        ppf.cut();
        ppf.cut();
        ppf.str("Possible solutions: ");
        ppf.cut();
        ppf.str("- Write out the full record with field and value, like: ");
        tagged(ppf, TAG_INFO, rewrite.as_deref().unwrap_or(""));
        ppf.cut();
        ppf.str("- Return the expected record from the block");
        return;
    }
    // | _, Some ({desc = Tconstr (p1)}, {desc = Tvariant row_desc}) when p1 = string
    if is(&p1, predef::path_string())
        && let TypeDesc::Tvariant(row) = &d2
    {
        let text = extract_text_at_loc(arena, source, loc);
        if let Some(string_value) = extract_string_constant(ctx, &text) {
            let variant_constructors: Vec<String> =
                row.row_fields.iter().map(|(l, _)| l.to_string()).collect();
            let reprinted = reprint_expr_at_loc(ctx, arena, source, loc, |sub_arena, exp| {
                let crate::parser::ast::ExpressionDesc::Pexp_constant(c) = &exp.pexp_desc else {
                    return None;
                };
                let crate::parser::ast::Constant::String(payload) = &*c else {
                    return None;
                };
                // The payload belongs to the re-parsed expression's arena.
                let s = payload.semantic(sub_arena).to_string();
                Some(crate::parser::ast::Expression {
                    pexp_desc: crate::parser::ast::ExpressionDesc::Pexp_variant(Box::new((
                        std::borrow::Cow::Owned(s),
                        crate::parse_arena::Located::new(
                            crate::parse_arena::ExprList::EMPTY,
                            exp.pexp_loc,
                        ),
                    ))),
                    ..exp
                })
            });
            if let Some(reprinted) = reprinted
                && variant_constructors.contains(&string_value)
            {
                raw(
                    ppf,
                    "\n\n  Possible solutions:\n  - The constant passed matches one of the expected polymorphic variant constructors. Did you mean to pass this as a polymorphic variant? If so, rewrite ",
                );
                tagged(ppf, TAG_INFO, &format!("\"{string_value}\""));
                raw(ppf, " to ");
                tagged(ppf, TAG_INFO, &reprinted);
            }
        }
        return;
    }
    // | _, Some ({desc = Tconstr (p1)}, ({desc = Tconstr _} as t2)) when p1 = string && is_variant_type t2
    if is(&p1, predef::path_string()) && p2.is_some() && is_variant_type(ctx, env, b2) {
        let text = extract_text_at_loc(arena, source, loc);
        if let Some(string_value) = extract_string_constant(ctx, &text)
            && let Some(decl) = extract_concrete_typedecl(ctx, env, b2)
            && let crate::types::decl::TypeKind::TypeVariant(constructors, layout) = &decl.type_kind
        {
            let layout = ctx.with_variant_layout(*layout, |l| l.clone());
            let matching = constructors.iter().enumerate().find_map(|(position, cd)| {
                let constructor_name = cd.cd_id.name().to_string();
                let runtime_repr = match constructor_tag(&layout, position) {
                    Some(crate::types::variant_runtime::LiteralTag::String(s)) => Some(s),
                    Some(_) => None,
                    None => Some(constructor_name.clone()),
                };
                (runtime_repr.as_deref() == Some(string_value.as_str())).then_some(constructor_name)
            });
            if let Some(constructor_name) = matching {
                let reprinted = reprint_expr_at_loc(ctx, arena, source, loc, |a, exp| {
                    if !matches!(&exp.pexp_desc, crate::parser::ast::ExpressionDesc::Pexp_constant(c)
                        if matches!(&*c, crate::parser::ast::Constant::String(..)))
                    {
                        return None;
                    }
                    let lid = a.push_lident(&constructor_name);
                    Some(crate::parser::ast::Expression {
                        pexp_desc: crate::parser::ast::ExpressionDesc::Pexp_construct(
                            crate::parser::ast::Loc {
                                txt: lid,
                                loc: exp.pexp_loc,
                            },
                            crate::parse_arena::Located::new(
                                crate::parse_arena::ExprList::EMPTY,
                                exp.pexp_loc,
                            ),
                        ),
                        ..exp
                    })
                });
                if let Some(reprinted) = reprinted {
                    raw(
                        ppf,
                        "\n\n  Possible solutions:\n  - The constant passed matches the runtime representation of one of the expected variant constructors. Did you mean to pass this as a variant constructor? If so, rewrite ",
                    );
                    tagged(ppf, TAG_INFO, &format!("\"{string_value}\""));
                    raw(ppf, " to ");
                    tagged(ppf, TAG_INFO, &reprinted);
                }
            }
        }
        return;
    }
    // | _, Some (_supplied_type, target_type) -> coercion suggestion
    let top_level_types = match trace {
        [(_, t1_top), (_, t2_top), ..] => Some((*t1_top, *t2_top)),
        _ => None,
    };
    let can_show_coercion_message = match top_level_types {
        Some((t1, t2)) => {
            if matches!(desc(t1), TypeDesc::Tvariant(_))
                && matches!(desc(t2), TypeDesc::Tvariant(_))
            {
                false
            } else {
                crate::types::ctype::subtype_now(ctx, env, t1, t2).is_ok()
            }
        }
        None => false,
    };
    let target_type_string = {
        printer.reset_and_mark_loops(b2);
        printer.type_expr(b2)
    };
    let target_expr_text = extract_text_at_loc(arena, source, loc);
    let suggested_rewrite = parse_and_reprint(
        ctx,
        &format!("({target_expr_text} :> {target_type_string})"),
    );
    let is_constant = text_is_constant(ctx, &target_expr_text);
    if can_show_coercion_message && !is_constant {
        ppf.cut();
        ppf.cut();
        ppf.str("Possible solutions: ");
        ppf.cut();
        ppf.str("- These types are compatible at runtime. You can use the coercion operator to convert to the expected type");
        match suggested_rewrite {
            Some(rewrite) => {
                ppf.str(": ");
                tagged(ppf, TAG_INFO, &rewrite);
                ppf.cut();
            }
            None => {
                ppf.str(": ");
                tagged(ppf, TAG_INFO, ":>");
                ppf.cut();
            }
        }
    }
}

/// `Variant_runtime.constructor_tag layout position`.
fn constructor_tag(
    layout: &crate::types::variant_runtime::Layout,
    position: usize,
) -> Option<crate::types::variant_runtime::LiteralTag> {
    match layout.constructors.get(position)? {
        crate::types::variant_runtime::ConstructorCase::Constant(tag) => tag.literal.clone(),
        crate::types::variant_runtime::ConstructorCase::Block(block) => block.tag().literal.clone(),
    }
}

/// `show_extra_help` (typecore.ml:738-748).
fn show_extra_help(ctx: &TypeContext, ppf: &mut Ppf<'_>, tr: &[TracePair]) {
    let Some((a, e)) = bottom_aliases(tr) else {
        return;
    };
    let (an, en) = match (&*ctx.borrow_desc(a), &*ctx.borrow_desc(e)) {
        (
            TypeDesc::Tconstr {
                path: Path::Pident(ai),
                args: aa,
                ..
            },
            TypeDesc::Tconstr {
                path: Path::Pident(ei),
                args: ea,
                ..
            },
        ) if aa.is_empty() && ea.is_empty() => (ai.name().to_string(), ei.name().to_string()),
        _ => return,
    };
    let converter = match (an.as_str(), en.as_str()) {
        ("float", "int") => Some("Float.toInt"),
        ("float", "string") => Some("Float.toString"),
        ("int", "float") => Some("Int.toFloat"),
        ("int", "string") => Some("Int.toString"),
        ("string", "float") => Some("Float.fromString"),
        ("string", "int") => Some("Int.fromString"),
        _ => None,
    };
    if let Some(converter) = converter {
        ppf.cut();
        ppf.cut();
        ppf.open_box(BoxKind::V, 2);
        ppf.str("You can convert ");
        tagged(ppf, TAG_INFO, &an);
        ppf.str(" to ");
        tagged(ppf, TAG_INFO, &en);
        ppf.str(" with ");
        tagged(ppf, TAG_INFO, converter);
        ppf.str(".");
        ppf.close_box();
    }
    match (an.as_str(), en.as_str()) {
        ("float", "int") => {
            ppf.space();
            ppf.str("If this is a literal, try a number without a trailing dot (e.g. ");
            tagged(ppf, TAG_INFO, "20");
            ppf.str(").");
        }
        ("int", "float") => {
            ppf.space();
            ppf.str("If this is a literal, try a number with a trailing dot (e.g. ");
            tagged(ppf, TAG_INFO, "20.");
            ppf.str(").");
        }
        _ => {}
    }
}

/// `print_expr_type_clash ~context env loc trace ppf` (typecore.ml:762-820)
/// inside `report_error`'s `@[<v>...@]`.
#[allow(clippy::too_many_arguments)]
pub(super) fn print_expr_type_clash(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    env: &Env,
    arena: &ParseArena,
    source: &str,
    loc: LocIdx,
    raw_trace: &[(TypeExprRef, TypeExprRef)],
    context: &Option<TypeClashContext>,
) {
    let tr = expand_trace(ctx, raw_trace);
    let mut printer = printer_with_env(ctx, env);
    ppf.open_box(BoxKind::V, 0);
    let bottom = bottom_aliases(&tr);
    let missing_arguments = bottom.and_then(|(a, e)| collect_missing_arguments(ctx, env, a, e));
    match missing_arguments.as_deref() {
        Some([single]) => {
            ppf.open_box(BoxKind::Box, 0);
            tagged(ppf, TAG_INFO, "This call is missing an argument");
            ppf.str(" of type");
            ppf.space();
            print_arguments(ppf, &mut printer, std::slice::from_ref(single));
            ppf.close_box();
        }
        Some(arguments) => {
            ppf.open_box(BoxKind::HV, 0);
            tagged(ppf, TAG_INFO, "This call is missing arguments");
            ppf.str(" of type:");
            ppf.space();
            print_arguments(ppf, &mut printer, arguments);
            ppf.close_box();
        }
        None => {
            let missing_parameters =
                bottom.and_then(|(a, e)| collect_missing_arguments(ctx, env, e, a));
            match missing_parameters.as_deref() {
                Some([single]) => {
                    ppf.open_box(BoxKind::Box, 0);
                    ppf.str("This value might need to be ");
                    open_tag(ppf, TAG_INFO);
                    ppf.str("wrapped in a function");
                    ppf.space();
                    ppf.str("that");
                    ppf.space();
                    ppf.str("takes");
                    ppf.space();
                    ppf.str("an");
                    ppf.space();
                    ppf.str("extra");
                    ppf.space();
                    ppf.str("parameter");
                    close_tag(ppf);
                    ppf.space();
                    ppf.str("of");
                    ppf.space();
                    ppf.str("type");
                    ppf.space();
                    print_arguments(ppf, &mut printer, std::slice::from_ref(single));
                    ppf.close_box();
                    ppf.cut();
                    ppf.cut();
                    ppf.open_box(BoxKind::Box, 0);
                    tagged(ppf, TAG_INFO, "Here's the original error message");
                    ppf.close_box();
                    ppf.cut();
                }
                Some(arguments) => {
                    ppf.open_box(BoxKind::Box, 0);
                    ppf.str("This value seems to ");
                    open_tag(ppf, TAG_INFO);
                    ppf.str("need to be wrapped in a function that takes extra");
                    ppf.space();
                    ppf.str("arguments");
                    close_tag(ppf);
                    ppf.space();
                    ppf.str("of");
                    ppf.space();
                    ppf.str("type:");
                    ppf.space();
                    ppf.open_box(BoxKind::HV, 0);
                    print_arguments(ppf, &mut printer, arguments);
                    ppf.close_box();
                    ppf.close_box();
                    ppf.cut();
                    ppf.cut();
                    ppf.open_box(BoxKind::Box, 0);
                    tagged(ppf, TAG_INFO, "Here's the original error message");
                    ppf.close_box();
                    ppf.cut();
                }
                None => {}
            }
            printer.super_unification_error(
                ppf,
                true,
                &tr,
                &mut |ppf| error_type_text(ppf, context),
                &mut |ppf| error_expected_type_text(ppf, context),
                None,
            );
            print_extra_type_clash_help(
                ppf,
                &mut printer,
                ctx,
                env,
                arena,
                source,
                loc,
                bottom,
                &tr,
                context,
            );
            show_extra_help(ctx, ppf, &tr);
        }
    }
    ppf.close_box();
}

/// `report_error`'s `Expr_type_clash` arity case (typecore.ml:4879-4889):
/// the expanded heads of the first two trace entries are arrows of
/// different arity.
pub(super) fn expr_type_clash_arity_mismatch(
    ctx: &TypeContext,
    raw_trace: &[(TypeExprRef, TypeExprRef)],
) -> Option<(usize, usize)> {
    let tr = expand_trace(ctx, raw_trace);
    let [(_, a), (_, b), ..] = tr.as_slice() else {
        return None;
    };
    match (&*ctx.borrow_desc(*a), &*ctx.borrow_desc(*b)) {
        (TypeDesc::Tarrow { args: pa, .. }, TypeDesc::Tarrow { args: pb, .. })
            if pa.len() != pb.len() =>
        {
            Some((pa.len(), pb.len()))
        }
        _ => None,
    }
}

/// `Typecore.report_error`'s `Not_subtype (tr1, tr2, ctx)`
/// (typecore.ml:4994-4995): `report_subtyping_error ppf env tr1
/// "is not a subtype of" tr2 ctx`.
pub(super) fn print_not_subtype(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    env: &Env,
    raw_trace1: &[(TypeExprRef, TypeExprRef)],
    raw_trace2: &[(TypeExprRef, TypeExprRef)],
    context: Option<&crate::types::SubtypeContext>,
) {
    let tr1 = expand_trace(ctx, raw_trace1);
    let tr2 = expand_trace(ctx, raw_trace2);
    let mut printer = printer_with_env(ctx, env);
    printer.report_subtyping_error(ppf, &tr1, "is not a subtype of", &tr2, context);
}

/// `Typetexp.report_error`'s `Constructor_mismatch (ty, ty')`
/// (typetexp.ml:804-809).
pub(super) fn print_constructor_mismatch(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    ty: TypeExprRef,
    ty2: TypeExprRef,
) {
    let mut printer = Printtyp::new(ctx);
    printer.reset_and_mark_loops_list(&[ty, ty2]);
    ppf.open_box(BoxKind::HOV, 0);
    ppf.str("This variant type contains a constructor");
    ppf.str(" ");
    printer.pp_type_expr(ppf, ty);
    ppf.space();
    ppf.str("which should be");
    ppf.space();
    printer.pp_type_expr(ppf, ty2);
    ppf.close_box();
}

/// `Typetexp.report_error`'s `Not_a_variant ty` (typetexp.ml:810-816).
pub(super) fn print_not_a_variant(ppf: &mut Ppf<'_>, ctx: &TypeContext, ty: TypeExprRef) {
    let mut printer = Printtyp::new(ctx);
    printer.reset_and_mark_loops(ty);
    ppf.open_box(BoxKind::Box, 0);
    ppf.str("The type ");
    printer.pp_type_expr(ppf, ty);
    ppf.space();
    ppf.str("does not expand to a polymorphic variant type");
    ppf.close_box();
    // `Misc.did_you_mean ppf (fun () -> ["`" ^ s])` (PR#7012).
    if let TypeDesc::Tvar(Some(name)) = &*ctx.get_desc(ctx.repr(ty)) {
        let name = name.clone();
        ppf.flush();
        ppf.newline();
        ppf.str(&format!("Hint: Did you mean `{name}?"));
        ppf.flush();
    }
}

/// `Typetexp.report_error`'s `Method_mismatch (l, ty, ty')`
/// (typetexp.ml:833-837).
pub(super) fn print_method_mismatch(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    label: &str,
    ty: TypeExprRef,
    ty2: TypeExprRef,
) {
    let mut printer = Printtyp::new(ctx);
    printer.reset_and_mark_loops_list(&[ty, ty2]);
    ppf.open_box(BoxKind::HOV, 0);
    ppf.str(&format!("Method '{label}' has type "));
    printer.pp_type_expr(ppf, ty);
    ppf.str(",");
    ppf.space();
    ppf.str("which should be ");
    printer.pp_type_expr(ppf, ty2);
    ppf.close_box();
}

/// `Error_message_utils.print_contextual_unification_error`
/// (error_message_utils.ml:859-882), the `print_extra_info` of pattern type
/// clashes.
fn print_contextual_unification_error(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    t1: TypeExprRef,
    t2: TypeExprRef,
) {
    let option = predef::path_option();
    let path_of = |t: TypeExprRef| match &*ctx.borrow_desc(t) {
        TypeDesc::Tconstr { path, .. } => Some(path.clone()),
        _ => None,
    };
    let (Some(p1), Some(p2)) = (path_of(t1), path_of(t2)) else {
        return;
    };
    if p1.same(&option) && !p2.same(&option) {
        ppf.cut();
        ppf.newline();
        ppf.open_box(BoxKind::V, 0);
        ppf.str("You're expecting the value you're pattern matching on to be an ");
        tagged(ppf, TAG_INFO, "option");
        ppf.str(", but the value is actually not an option.");
        ppf.space();
        ppf.str("Change your pattern match to work on the concrete value (remove ");
        tagged(ppf, TAG_ERROR, "Some(_)");
        ppf.str(" or ");
        tagged(ppf, TAG_ERROR, "None");
        ppf.str(" from the pattern) to make it work.");
        ppf.close_box();
    } else if p2.same(&option) && !p1.same(&option) {
        ppf.cut();
        ppf.newline();
        ppf.open_box(BoxKind::V, 0);
        ppf.str("The value you're pattern matching on here is wrapped in an ");
        tagged(ppf, TAG_INFO, "option");
        ppf.str(", but you're trying to match on the actual value.");
        ppf.space();
        ppf.str("Wrap the highlighted pattern in ");
        tagged(ppf, TAG_INFO, "Some()");
        ppf.str(" to make it work.");
        ppf.close_box();
    }
}

fn printer_with_env<'c>(ctx: &'c TypeContext, env: &Env) -> Printtyp<'c> {
    let mut printer = Printtyp::new(ctx);
    let lookup_env = env.clone();
    printer.set_printing_env(Box::new(move |name| {
        lookup_env.find_type_with_path(name).ok().map(|(p, _)| p)
    }));
    printer
}

/// `Typecore.report_error`'s `Pattern_type_clash trace`
/// (typecore.ml:4855-4863).
pub(super) fn print_pattern_type_clash(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    env: &Env,
    raw_trace: &[(TypeExprRef, TypeExprRef)],
) {
    let tr = expand_trace(ctx, raw_trace);
    let mut printer = printer_with_env(ctx, env);
    let mut extra = |ppf: &mut Ppf<'_>, _: &mut Printtyp<'_>, t1: TypeExprRef, t2: TypeExprRef| {
        print_contextual_unification_error(ppf, ctx, t1, t2)
    };
    printer.super_unification_error(
        ppf,
        true,
        &tr,
        &mut |ppf| ppf.str("This pattern matches values of type"),
        &mut |ppf| ppf.str("but a pattern was expected which matches values of type"),
        Some(&mut extra),
    );
}

/// `Typecore.report_error`'s `Less_general (kind, trace)`
/// (typecore.ml:5012-5016).
pub(super) fn print_less_general(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    env: &Env,
    kind: &str,
    tr: &[(TypeExprRef, TypeExprRef)],
) {
    let mut printer = printer_with_env(ctx, env);
    let first = format!("This {kind} has type");
    printer.super_unification_error(
        ppf,
        true,
        tr,
        &mut |ppf| ppf.str(&first),
        &mut |ppf| ppf.str("which is less general than"),
        None,
    );
}

/// `Typecore.report_error`'s `Or_pattern_type_clash (id, trace)`
/// (typecore.ml:4864-4872).
pub(super) fn print_or_pattern_type_clash(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    env: &Env,
    name: &str,
    raw_trace: &[(TypeExprRef, TypeExprRef)],
) {
    let tr = expand_trace(ctx, raw_trace);
    let mut printer = printer_with_env(ctx, env);
    let first = format!("The variable {name} on the left-hand side of this or-pattern has type");
    printer.super_unification_error(
        ppf,
        true,
        &tr,
        &mut |ppf| ppf.str(&first),
        &mut |ppf| ppf.str("but on the right-hand side it has type"),
        None,
    );
}

/// `Typecore.report_error`'s `Apply_non_function typ` (typecore.ml:4895-4923).
/// Typecore's `type_expr`: `Error_message_utils.type_expr`
/// (error_message_utils.ml:72-75), which resets the printer and marks loops,
/// normalizing the type, before printing it.
fn typecore_type_expr(ppf: &mut Ppf<'_>, printer: &mut Printtyp<'_>, ty: TypeExprRef) {
    printer.reset_and_mark_loops(ty);
    printer.pp_type_expr(ppf, ty);
}

pub(super) fn print_apply_non_function(ppf: &mut Ppf<'_>, ctx: &TypeContext, typ: TypeExprRef) {
    let mut printer = Printtyp::new(ctx);
    let repr = ctx.repr(typ);
    let desc = (*ctx.get_desc(repr)).clone();
    match desc {
        TypeDesc::Tarrow { args, ret } => {
            let mut count = args.len();
            let mut next = ret;
            while let TypeDesc::Tarrow { args, ret } = &*ctx.borrow_desc(next) {
                count += args.len();
                next = *ret;
            }
            ppf.open_box(BoxKind::V, 0);
            ppf.open_box(BoxKind::Box, 2);
            ppf.str("This function has type");
            ppf.space();
            open_tag(ppf, TAG_INFO);
            typecore_type_expr(ppf, &mut printer, typ);
            close_tag(ppf);
            ppf.close_box();
            ppf.space();
            ppf.open_box(BoxKind::Box, 0);
            ppf.str(&format!(
                "It only accepts {count} {}; here, it's called with more.",
                if count == 1 { "argument" } else { "arguments" }
            ));
            ppf.close_box();
            ppf.close_box();
        }
        TypeDesc::Tconstr { path, .. } if path.same(&predef::path_tagged_template()) => {
            ppf.open_box(BoxKind::V, 0);
            ppf.open_box(BoxKind::Box, 2);
            ppf.str("This is a tagged-template tag of type");
            ppf.space();
            open_tag(ppf, TAG_INFO);
            typecore_type_expr(ppf, &mut printer, typ);
            close_tag(ppf);
            ppf.close_box();
            ppf.cut();
            ppf.str(
                "It can't be called like a function. Use it with backtick syntax instead, e.g. ",
            );
            tagged(ppf, TAG_INFO, "tag`SELECT ${id}`");
            ppf.str(".");
            ppf.close_box();
        }
        _ => {
            ppf.open_box(BoxKind::V, 0);
            ppf.open_box(BoxKind::Box, 2);
            ppf.str("This can't be called, it's not a function.");
            ppf.close_box();
            ppf.cut();
            ppf.str("It has type: ");
            typecore_type_expr(ppf, &mut printer, typ);
            ppf.close_box();
        }
    }
}

/// `Typecore.report_error`'s `Apply_wrong_label (l, ty)` (typecore.ml:4924-4932);
/// `label` is `None` for `Nolabel`, else the prefixed label name.
pub(super) fn print_apply_wrong_label(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    label: Option<&str>,
    ty: TypeExprRef,
) {
    let mut printer = Printtyp::new(ctx);
    ppf.open_box(BoxKind::V, 0);
    ppf.open_box(BoxKind::Box, 2);
    match label {
        None => ppf.str("The argument at this position should be labelled."),
        Some(label) => {
            ppf.str("This function does not take the argument ");
            tagged(ppf, TAG_INFO, label);
            ppf.str(".");
        }
    }
    ppf.close_box();
    ppf.cut();
    ppf.str("This function has type: ");
    typecore_type_expr(ppf, &mut printer, ty);
    ppf.close_box();
}

/// `Typecore.report_error`'s `Abstract_wrong_label (l, ty)` (typecore.ml:4996-5003).
pub(super) fn print_abstract_wrong_label(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    label_mark: &str,
    ty: TypeExprRef,
) {
    let mut printer = Printtyp::new(ctx);
    ppf.open_box(BoxKind::V, 0);
    ppf.open_box(BoxKind::Box, 2);
    ppf.str("This function should have type");
    ppf.space();
    typecore_type_expr(ppf, &mut printer, ty);
    ppf.close_box();
    ppf.cut();
    ppf.str(label_mark);
    ppf.close_box();
}

/// `Typecore.report_error`'s `Field_not_optional (name, typ)` (typecore.ml:5222-5224).
pub(super) fn print_field_not_optional(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    name: &str,
    typ: TypeExprRef,
) {
    let mut printer = Printtyp::new(ctx);
    ppf.str("Field ");
    tagged(ppf, TAG_INFO, name);
    ppf.str(" is not optional in type ");
    typecore_type_expr(ppf, &mut printer, typ);
    ppf.str(". Use without ?");
}

/// `Typecore.report_error`'s `Tagged_template_non_tag typ` (typecore.ml:5237-5250).
pub(super) fn print_tagged_template_non_tag(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    typ: TypeExprRef,
) {
    let mut printer = Printtyp::new(ctx);
    ppf.open_box(BoxKind::V, 0);
    ppf.str("This value is used with tagged template (backtick) syntax, but it has type");
    ppf.space();
    open_tag(ppf, TAG_INFO);
    typecore_type_expr(ppf, &mut printer, typ);
    close_tag(ppf);
    ppf.space();
    ppf.str("which is not a ");
    tagged(ppf, TAG_INFO, "taggedTemplate");
    ppf.str(".");
    ppf.cut();
    ppf.cut();
    ppf.str("Tagged template syntax now requires a value of type ");
    tagged(ppf, TAG_INFO, "taggedTemplate<'param, 'output>");
    ppf.str(":");
    ppf.cut();
    ppf.cut();
    ppf.str("  - To bind a JavaScript tag function, annotate the ");
    tagged(ppf, TAG_INFO, "external");
    ppf.str(" with ");
    tagged(ppf, TAG_INFO, "taggedTemplate<...>");
    ppf.str(" instead of using the removed ");
    tagged(ppf, TAG_INFO, "@taggedTemplate");
    ppf.str(" decorator.");
    ppf.cut();
    ppf.str("  - To use a ReScript function as a tag, lift it with ");
    tagged(ppf, TAG_INFO, "TaggedTemplate.make");
    ppf.str(".");
    ppf.close_box();
}

/// `Printtyp.report_unification_error ppf Env.empty trace txt1 txt2`.
pub(super) fn print_report_unification_error(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    raw_trace: &[(TypeExprRef, TypeExprRef)],
    txt1: &str,
    txt2: &str,
) {
    let tr = expand_trace(ctx, raw_trace);
    let mut printer = Printtyp::new(ctx);
    printer.report_unification_error(ppf, true, &tr, txt1, txt2);
}

/// `Typecore.report_error`'s `Name_type_mismatch (kind, lid, tp, tpl)`
/// (typecore.ml:4973-4986).
pub(super) fn print_name_type_mismatch(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    env: Option<&Env>,
    kind: &str,
    lid: &str,
    tp: &(Path, Path),
    tpl: &[(Path, Path)],
) {
    let mut printer = match env {
        Some(env) => printer_with_env(ctx, env),
        None => Printtyp::new(ctx),
    };
    let name = if kind == "record" {
        "field"
    } else {
        "constructor"
    };
    printer.report_ambiguous_type_error(
        ppf,
        tp,
        tpl,
        &mut |ppf| {
            ppf.str(&format!("The {name} {lid}"));
            ppf.space();
            ppf.str(&format!("belongs to the {kind} type"));
        },
        &mut |ppf| {
            ppf.str(&format!("The {name} {lid}"));
            ppf.space();
            ppf.str(&format!("belongs to one of the following {kind} types:"));
        },
        &mut |ppf| {
            ppf.str(&format!(
                "but a {name} was expected belonging to the {kind} type"
            ))
        },
    );
}

/// `Misc.did_you_mean ppf choices` (misc.ml:259-270) with the choices
/// already joined.
fn did_you_mean(ppf: &mut Ppf<'_>, hint: Option<&str>) {
    ppf.flush();
    if let Some(hint) = hint {
        ppf.newline();
        ppf.str(&format!("Hint: Did you mean {hint}?"));
        ppf.flush();
    }
}

/// `Typetexp.report_error`'s `Unbound_label (lid, from_type)`
/// (typetexp.ml:906-949), followed by its `spellcheck` hint.
pub(super) fn print_unbound_label(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    lid: &str,
    from_type: Option<TypeExprRef>,
    hint: Option<&str>,
) {
    let from_path = from_type.and_then(|ty| match &*ctx.get_desc(ctx.repr(ty)) {
        TypeDesc::Tconstr { path, .. } => Some(path.clone()),
        _ => None,
    });
    match from_path {
        Some(path) if path.same(&predef::path_option()) => {
            ppf.open_box(BoxKind::V, 0);
            ppf.str("You're trying to access the record field ");
            tagged(ppf, TAG_INFO, lid);
            ppf.str(", but the value you're trying to access it on is an ");
            tagged(ppf, TAG_INFO, "option");
            ppf.str(".");
            ppf.space();
            ppf.str("You need to unwrap the option first before accessing the record field.");
            ppf.cut();
            ppf.newline();
            ppf.str("Possible solutions:");
            ppf.cut();
            ppf.open_box(BoxKind::Box, 0);
            ppf.str("- Use ");
            tagged(ppf, TAG_INFO, "Option.map");
            ppf.str(" to transform the option: ");
            tagged(
                ppf,
                TAG_INFO,
                &format!("xx->Option.map(field => field.{lid})"),
            );
            ppf.close_box();
            ppf.cut();
            ppf.open_box(BoxKind::Box, 0);
            ppf.str("- Or use ");
            tagged(ppf, TAG_INFO, "Option.getOr");
            ppf.str(" with a default: ");
            tagged(
                ppf,
                TAG_INFO,
                &format!("xx->Option.getOr(defaultRecord).{lid}"),
            );
            ppf.close_box();
            ppf.close_box();
        }
        Some(path) if path.same(&predef::path_array()) => {
            ppf.open_box(BoxKind::V, 0);
            ppf.str("You're trying to access the record field ");
            tagged(ppf, TAG_INFO, lid);
            ppf.str(", but the value you're trying to access it on is an ");
            tagged(ppf, TAG_INFO, "array");
            ppf.str(".");
            ppf.space();
            ppf.str(
                "You need to access an individual element of the array if you want to access an individual record field.",
            );
            ppf.close_box();
        }
        Some(_) => {
            let ty = from_type.expect("from_path implies from_type");
            let mut printer = Printtyp::new(ctx);
            ppf.open_box(BoxKind::V, 0);
            ppf.str("You're trying to access the record field ");
            tagged(ppf, TAG_INFO, lid);
            ppf.str(", but the thing you're trying to access it on is not a record. ");
            ppf.cut();
            raw(ppf, "\n");
            ppf.str("The type of the thing you're trying to access it on is:");
            ppf.cut();
            raw(ppf, "\n");
            typecore_type_expr(ppf, &mut printer, ty);
            ppf.cut();
            raw(ppf, "\n");
            ppf.cut();
            ppf.str("Only records have fields that can be accessed with dot notation.");
            ppf.close_box();
        }
        None => {
            ppf.open_box(BoxKind::V, 0);
            tagged(ppf, TAG_INFO, lid);
            ppf.str(" refers to a record field, but no corresponding record type is in scope.");
            ppf.cut();
            ppf.cut();
            ppf.str("If it's defined in another module or file, bring it into scope by:");
            ppf.cut();
            ppf.open_box(BoxKind::Box, 0);
            ppf.str("- Prefixing the field name with the module name:");
            ppf.space();
            tagged(ppf, TAG_INFO, &format!("TheModule.{lid}"));
            ppf.close_box();
            ppf.cut();
            ppf.open_box(BoxKind::Box, 0);
            ppf.str("- Or specifying the record type explicitly:");
            ppf.space();
            tagged(
                ppf,
                TAG_INFO,
                &format!("let theValue: TheModule.theType = {{{lid}: VALUE}}"),
            );
            ppf.close_box();
            ppf.close_box();
        }
    }
    did_you_mean(ppf, hint);
}

/// `Typetexp.report_error`'s `Unbound_constructor lid` (typetexp.ml:891-904),
/// followed by its `spellcheck` hint.
pub(super) fn print_unbound_constructor(ppf: &mut Ppf<'_>, lid: &str, hint: Option<&str>) {
    ppf.open_box(BoxKind::V, 0);
    tagged(
        ppf,
        TAG_INFO,
        &format!("The variant constructor {lid} can't be found."),
    );
    ppf.cut();
    ppf.cut();
    ppf.open_box(BoxKind::V, 2);
    ppf.str("- If it's defined in another module or file, bring it into scope by:");
    ppf.cut();
    ppf.open_box(BoxKind::Box, 0);
    ppf.str("- Prefixing it with said module name:");
    ppf.space();
    tagged(ppf, TAG_INFO, &format!("TheModule.{lid}"));
    ppf.close_box();
    ppf.cut();
    ppf.open_box(BoxKind::Box, 0);
    ppf.str("- Or specifying its type:");
    ppf.space();
    tagged(
        ppf,
        TAG_INFO,
        &format!("let theValue: TheModule.theType = {lid}"),
    );
    ppf.close_box();
    ppf.close_box();
    ppf.cut();
    ppf.str("- ");
    ppf.open_box(BoxKind::Box, 0);
    ppf.str("Constructors and modules are both capitalized.");
    ppf.space();
    ppf.str("Did you want the latter?");
    ppf.space();
    ppf.str("Then instead of ");
    tagged(ppf, crate::types::printtyp::TAG_DIM, "let foo = Bar");
    ppf.str(", try ");
    tagged(ppf, TAG_INFO, "module Foo = Bar");
    ppf.str(".");
    ppf.close_box();
    ppf.close_box();
    did_you_mean(ppf, hint);
}

/// `Wrong_name` for the field of a constructor's inline record
/// (typecore.ml:4957-4961) followed by `spellcheck ppf name valid_names`.
pub(super) fn print_wrong_name_inline_record_field(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    name: &str,
    path: &Path,
    hint: Option<&str>,
) {
    let printer = Printtyp::new(ctx);
    ppf.open_box(BoxKind::Box, 0);
    ppf.str(&format!(
        "The field {name} is not part of the record argument for the {} constructor",
        printer.path_text(path)
    ));
    ppf.close_box();
    did_you_mean(ppf, hint);
}

/// `Typecore.report_error`'s `Labels_missing` (typecore.ml:4942-4947) and
/// `Error_message_utils.print_component_labels_missing_error`
/// (error_message_utils.ml:933-939).
pub(super) fn print_labels_missing(
    ppf: &mut Ppf<'_>,
    labels: &[String],
    component_name: Option<Option<&str>>,
) {
    ppf.open_box(BoxKind::HOV, 0);
    match component_name {
        Some(component_name) => {
            ppf.str("The component ");
            // `print_component_name` (error_message_utils.ml:914-917).
            if let Some(name) = component_name {
                tagged(ppf, TAG_INFO, &format!("<{name} />"));
                ppf.str(" ");
            }
            ppf.str("is missing these required props:");
            ppf.newline();
            for label in labels {
                ppf.space();
                ppf.str(label);
            }
        }
        None => {
            ppf.str("Some required record fields are missing:");
            for label in labels {
                ppf.space();
                ppf.str(label);
            }
            ppf.str(".");
        }
    }
    ppf.close_box();
}

/// `Typecore.report_error`'s `Undefined_method (ty, me, valid_methods)`
/// (typecore.ml:4987-4993).
pub(super) fn print_undefined_method(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    ty: TypeExprRef,
    method: &str,
    hint: Option<Option<&str>>,
) {
    let mut printer = Printtyp::new(ctx);
    ppf.open_box(BoxKind::V, 0);
    ppf.open_box(BoxKind::Box, 0);
    ppf.str("This expression has type");
    ppf.break_(1, 2);
    typecore_type_expr(ppf, &mut printer, ty);
    ppf.close_box();
    ppf.cut();
    ppf.str(&format!("It has no field {method}"));
    ppf.close_box();
    if let Some(hint) = hint {
        did_you_mean(ppf, hint);
    }
}

/// `Typecore.report_error`'s `Object_field_not_mutable (ty, name)`.
pub(super) fn print_object_field_not_mutable(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    ty: TypeExprRef,
    name: &str,
) {
    let mut printer = Printtyp::new(ctx);
    ppf.open_box(BoxKind::V, 0);
    ppf.open_box(BoxKind::Box, 0);
    ppf.str("This expression has type");
    ppf.break_(1, 2);
    typecore_type_expr(ppf, &mut printer, ty);
    ppf.close_box();
    ppf.cut();
    ppf.str(&format!(
        "The field {name} is not settable. Only fields annotated with @set, e.g. {{@set \"{name}\": int}}, can be assigned."
    ));
    ppf.close_box();
}

/// `Typedecl.report_error`'s `Definition_mismatch (ty, errs)`
/// (typedecl.ml:2153-2159); `detail` is the rendered
/// `Includecore.report_type_mismatch` sentence, if any.
pub(super) fn print_definition_mismatch(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    ty: TypeExprRef,
    detail: Option<&str>,
) {
    let mut printer = Printtyp::new(ctx);
    ppf.open_box(BoxKind::V, 0);
    ppf.open_box(BoxKind::HOV, 0);
    ppf.str("This variant or record definition");
    ppf.space();
    ppf.str("does not match that of type");
    ppf.break_(1, 2);
    typecore_type_expr(ppf, &mut printer, ty);
    ppf.close_box();
    if let Some(detail) = detail.filter(|detail| !detail.is_empty()) {
        // `report_type_mismatch` prints each error as "@ %a.".
        // Breaks inside an error ("Their internal representations differ:@ ...")
        // are hints of the enclosing vertical box.
        for line in detail.split('\n') {
            ppf.space();
            ppf.str(line);
        }
    }
    ppf.close_box();
}

/// `Typedecl.explain_unbound_gen` for `explain_unbound ppf tv tl (fun c -> c)
/// "type" (fun _ -> "")` (typedecl.ml:2080-2094), without the leading ".@.":
/// `@[<hov2>In type@ %a@;<1 -2>the variable %a is unbound@]`, where the
/// types are marked together with `Tobject (tv, ref None)` to force aliasing.
pub(super) fn print_explain_unbound_type(
    ppf: &mut Ppf<'_>,
    ctx: &TypeContext,
    tv: TypeExprRef,
    ti: TypeExprRef,
) {
    let mut printer = Printtyp::new(ctx);
    let ty0 = ctx.new_generic_type(TypeDesc::Tobject { fields: tv });
    printer.reset_and_mark_loops_list(&[ti, ty0]);
    ppf.open_box(BoxKind::HOV, 2);
    ppf.str("In type");
    ppf.space();
    printer.pp_type_expr(ppf, ti);
    ppf.break_(1, -2);
    ppf.str("the variable ");
    printer.pp_type_expr(ppf, tv);
    ppf.str(" is unbound");
    ppf.close_box();
}
