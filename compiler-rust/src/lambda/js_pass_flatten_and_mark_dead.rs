//! JS IR pass: flatten and mark dead.
//!
//! This pass flattens nested block structures, substitutes caml block
//! projections, and marks dead code for elimination.

use ahash::AHashMap as HashMap;
use ahash::AHashSet as HashSet;

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::js_ir::op::{IdentInfo, MutableFlag, Number, UsedStats};
use crate::js_ir::{
    BinOp, Block, CaseClause, DepsProgram, Expression, ExpressionDesc, Program, Statement,
    StatementDesc, StringClause, VariableDeclaration,
};
use crate::lambda::TagInfo;
use crate::lambda::lam_compat::LetKind;

use super::js_exp_make::{
    direct_projection_from_pure_literal, int_literal, js_expr_no_side_effects,
};
use super::lam_coercion::max_ident_stamp_in_block;

pub(crate) fn apply_js_flatten_pass(mut deps: DepsProgram) -> DepsProgram {
    deps.program = flatten_program(deps.program);
    deps
}

pub(crate) fn apply_js_flatten_and_mark_dead_pass(
    mut deps: DepsProgram,
    jsx_preserve: bool,
) -> DepsProgram {
    // OCaml's substitution pass allocates materialized block fields with
    // `Ext_ident.create` from the process-wide Ident counter
    // (compiler/core/js_pass_flatten_and_mark_dead.ml:188-204). Keep Rust's
    // pass generator past both the JS program and the legacy local counter so
    // newly materialized fields cannot share stamps with existing locals.
    let start_stamp = max_ident_stamp_in_program(&deps.program).max(Ident::current_local_stamp());
    let id_gen = IdGenerator::with_start_stamp(start_stamp);
    Ident::set_current_time(start_stamp);
    deps.program = flatten_and_mark_dead_program(deps.program, &id_gen, jsx_preserve);
    deps
}

fn flatten_and_mark_dead_program(
    mut program: Program,
    id_gen: &IdGenerator,
    jsx_preserve: bool,
) -> Program {
    let mut substitution = HashMap::new();
    program.block =
        flatten_and_mark_dead_block(program.block, id_gen, &mut substitution, jsx_preserve);
    mark_dead_code(&mut program);
    program
}

fn flatten_and_mark_dead_block(
    block: Block,
    id_gen: &IdGenerator,
    substitution: &mut HashMap<Ident, Expression>,
    jsx_preserve: bool,
) -> Block {
    block
        .into_iter()
        .map(|stmt| flatten_and_mark_dead_statement(stmt, id_gen, substitution, jsx_preserve))
        .collect()
}

fn flatten_and_mark_dead_statement(
    stmt: Statement,
    id_gen: &IdGenerator,
    substitution: &mut HashMap<Ident, Expression>,
    jsx_preserve: bool,
) -> Statement {
    let Statement {
        source_loc,
        desc,
        comment,
    } = stmt;
    match desc {
        StatementDesc::Variable(decl) => {
            if matches!(decl.ident_info.used_stats, UsedStats::DeadPure) {
                return Statement {
                    source_loc,
                    desc: StatementDesc::Block(vec![]),
                    comment,
                };
            }

            if matches!(decl.ident_info.used_stats, UsedStats::DeadNonPure) {
                return match decl.value {
                    None => Statement {
                        source_loc,
                        desc: StatementDesc::Block(vec![]),
                        comment,
                    },
                    Some(value) => Statement {
                        source_loc,
                        desc: StatementDesc::Exp(value),
                        comment,
                    },
                };
            }

            if matches!(
                decl.property,
                LetKind::Strict | LetKind::StrictOpt | LetKind::Alias
            ) {
                if let Some(Expression {
                    source_loc: value_loc,
                    desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, tag_info),
                    comment: value_comment,
                }) = decl.value
                {
                    if should_materialize_block_binding_items(decl.property, &items, &tag_info) {
                        let mut rewritten_items = Vec::with_capacity(items.len());
                        let mut bindings = Vec::new();

                        for (index, item) in items.into_iter().enumerate() {
                            if is_simple_block_binding_item(&item) {
                                rewritten_items.push(item);
                            } else {
                                let rewritten = flatten_and_mark_dead_expression(
                                    item,
                                    id_gen,
                                    substitution,
                                    jsx_preserve,
                                );
                                let temp = id_gen.create(&block_substitution_name(
                                    &decl.ident,
                                    &tag_info,
                                    index,
                                ));
                                rewritten_items.push(Expression::var(temp));
                                bindings.push(Statement::variable(VariableDeclaration {
                                    ident: temp,
                                    value: Some(rewritten),
                                    property: LetKind::Strict,
                                    ident_info: IdentInfo::default(),
                                }));
                            }
                        }

                        let rewritten_value = Expression {
                            source_loc: value_loc,
                            desc: ExpressionDesc::CamlBlock(
                                rewritten_items,
                                MutableFlag::Immutable,
                                tag_info,
                            ),
                            comment: value_comment,
                        };
                        substitution.insert(decl.ident, rewritten_value.clone());

                        let original = Statement {
                            source_loc: source_loc.clone(),
                            desc: StatementDesc::Variable(VariableDeclaration {
                                ident: decl.ident,
                                value: Some(rewritten_value),
                                property: decl.property,
                                ident_info: decl.ident_info,
                            }),
                            comment,
                        };

                        if bindings.is_empty() {
                            return original;
                        }

                        bindings.push(original);
                        return Statement {
                            source_loc,
                            desc: StatementDesc::Block(bindings),
                            comment: None,
                        };
                    }

                    // OCaml's js_pass_flatten_and_mark_dead matches
                    // `_ :: _ :: _ as ls`, which means immutable Caml blocks
                    // with at least two payload elements. Polyvar wrappers stay
                    // out of this path because their exported `NAME`/`VAL`
                    // object shape is already materialized before this pass in
                    // the OCaml backend.
                    return Statement {
                        source_loc: source_loc.clone(),
                        desc: {
                            let rewritten_value = Expression {
                                source_loc: value_loc,
                                desc: ExpressionDesc::CamlBlock(
                                    items
                                        .into_iter()
                                        .map(|item| {
                                            flatten_and_mark_dead_expression(
                                                item,
                                                id_gen,
                                                substitution,
                                                jsx_preserve,
                                            )
                                        })
                                        .collect(),
                                    MutableFlag::Immutable,
                                    tag_info,
                                ),
                                comment: value_comment,
                            };
                            StatementDesc::Variable(VariableDeclaration {
                                ident: decl.ident,
                                value: Some(rewritten_value),
                                property: decl.property,
                                ident_info: decl.ident_info,
                            })
                        },
                        comment,
                    };
                }
            }

            Statement {
                source_loc,
                desc: StatementDesc::Variable(VariableDeclaration {
                    ident: decl.ident,
                    value: decl.value.map(|value| {
                        flatten_and_mark_dead_expression(value, id_gen, substitution, jsx_preserve)
                    }),
                    property: decl.property,
                    ident_info: decl.ident_info,
                }),
                comment,
            }
        }
        StatementDesc::Block(block) => Statement {
            source_loc,
            desc: StatementDesc::Block(flatten_and_mark_dead_block(
                block,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            comment,
        },
        StatementDesc::Exp(expr) => Statement {
            source_loc,
            desc: StatementDesc::Exp(flatten_and_mark_dead_expression(
                expr,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            comment,
        },
        StatementDesc::Return(expr) => Statement {
            source_loc,
            desc: StatementDesc::Return(flatten_and_mark_dead_expression(
                expr,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            comment,
        },
        StatementDesc::If(cond, then_block, else_block) => Statement {
            source_loc,
            desc: StatementDesc::If(
                flatten_and_mark_dead_expression(cond, id_gen, substitution, jsx_preserve),
                flatten_and_mark_dead_block(then_block, id_gen, substitution, jsx_preserve),
                flatten_and_mark_dead_block(else_block, id_gen, substitution, jsx_preserve),
            ),
            comment,
        },
        StatementDesc::While(label, cond, body) => Statement {
            source_loc,
            desc: StatementDesc::While(
                label,
                flatten_and_mark_dead_expression(cond, id_gen, substitution, jsx_preserve),
                flatten_and_mark_dead_block(body, id_gen, substitution, jsx_preserve),
            ),
            comment,
        },
        StatementDesc::ForRange(label, start, finish, ident, direction, body) => Statement {
            source_loc,
            desc: StatementDesc::ForRange(
                label,
                start.map(|expr| {
                    Box::new(flatten_and_mark_dead_expression(
                        *expr,
                        id_gen,
                        substitution,
                        jsx_preserve,
                    ))
                }),
                Box::new(flatten_and_mark_dead_expression(
                    *finish,
                    id_gen,
                    substitution,
                    jsx_preserve,
                )),
                ident,
                direction,
                flatten_and_mark_dead_block(body, id_gen, substitution, jsx_preserve),
            ),
            comment,
        },
        StatementDesc::ForOf(label, ident, iterable, body) => Statement {
            source_loc,
            desc: StatementDesc::ForOf(
                label,
                ident,
                Box::new(flatten_and_mark_dead_expression(
                    *iterable,
                    id_gen,
                    substitution,
                    jsx_preserve,
                )),
                flatten_and_mark_dead_block(body, id_gen, substitution, jsx_preserve),
            ),
            comment,
        },
        StatementDesc::ForAwaitOf(label, ident, iterable, body) => Statement {
            source_loc,
            desc: StatementDesc::ForAwaitOf(
                label,
                ident,
                Box::new(flatten_and_mark_dead_expression(
                    *iterable,
                    id_gen,
                    substitution,
                    jsx_preserve,
                )),
                flatten_and_mark_dead_block(body, id_gen, substitution, jsx_preserve),
            ),
            comment,
        },
        StatementDesc::IntSwitch(test, clauses, default) => Statement {
            source_loc,
            desc: StatementDesc::IntSwitch(
                flatten_and_mark_dead_expression(test, id_gen, substitution, jsx_preserve),
                clauses
                    .into_iter()
                    .map(|(tag, clause)| {
                        (
                            tag,
                            CaseClause {
                                source_loc: clause.source_loc,
                                body: flatten_and_mark_dead_block(
                                    clause.body,
                                    id_gen,
                                    substitution,
                                    jsx_preserve,
                                ),
                                should_break: clause.should_break,
                                comment: clause.comment,
                            },
                        )
                    })
                    .collect(),
                default.map(|block| {
                    flatten_and_mark_dead_block(block, id_gen, substitution, jsx_preserve)
                }),
            ),
            comment,
        },
        StatementDesc::StringSwitch(test, clauses, default) => Statement {
            source_loc,
            desc: StatementDesc::StringSwitch(
                flatten_and_mark_dead_expression(test, id_gen, substitution, jsx_preserve),
                clauses
                    .into_iter()
                    .map(|clause| crate::js_ir::StringClause {
                        tag_type: clause.tag_type,
                        clause: CaseClause {
                            source_loc: clause.clause.source_loc,
                            body: flatten_and_mark_dead_block(
                                clause.clause.body,
                                id_gen,
                                substitution,
                                jsx_preserve,
                            ),
                            should_break: clause.clause.should_break,
                            comment: clause.clause.comment,
                        },
                    })
                    .collect(),
                default.map(|block| {
                    flatten_and_mark_dead_block(block, id_gen, substitution, jsx_preserve)
                }),
            ),
            comment,
        },
        StatementDesc::Throw(expr) => Statement {
            source_loc,
            desc: StatementDesc::Throw(flatten_and_mark_dead_expression(
                expr,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            comment,
        },
        StatementDesc::Try(body, catch, finally) => Statement {
            source_loc,
            desc: StatementDesc::Try(
                flatten_and_mark_dead_block(body, id_gen, substitution, jsx_preserve),
                catch.map(|(ident, block)| {
                    (
                        ident,
                        flatten_and_mark_dead_block(block, id_gen, substitution, jsx_preserve),
                    )
                }),
                finally.map(|block| {
                    flatten_and_mark_dead_block(block, id_gen, substitution, jsx_preserve)
                }),
            ),
            comment,
        },
        StatementDesc::Debugger => Statement {
            source_loc,
            desc: StatementDesc::Debugger,
            comment,
        },
        StatementDesc::Break(label) => Statement {
            source_loc,
            desc: StatementDesc::Break(label),
            comment,
        },
        StatementDesc::Continue(label) => Statement {
            source_loc,
            desc: StatementDesc::Continue(label),
            comment,
        },
    }
}

fn flatten_and_mark_dead_expression(
    expr: Expression,
    id_gen: &IdGenerator,
    substitution: &mut HashMap<Ident, Expression>,
    jsx_preserve: bool,
) -> Expression {
    if let Some(rewritten) = try_substitute_caml_block_projection(&expr, substitution) {
        return rewritten;
    }

    let Expression {
        source_loc,
        desc,
        comment,
    } = expr;
    let desc = match desc {
        ExpressionDesc::Length(inner, object) => ExpressionDesc::Length(
            Box::new(flatten_and_mark_dead_expression(
                *inner,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            object,
        ),
        ExpressionDesc::IsNullOrUndefined(inner) => ExpressionDesc::IsNullOrUndefined(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::StringAppend(left, right) => ExpressionDesc::StringAppend(
            Box::new(flatten_and_mark_dead_expression(
                *left,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *right,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::Bool(value) => ExpressionDesc::Bool(value),
        ExpressionDesc::Typeof(inner) => ExpressionDesc::Typeof(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::In(left, right) => ExpressionDesc::In(
            Box::new(flatten_and_mark_dead_expression(
                *left,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *right,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::JsNot(inner) => ExpressionDesc::JsNot(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::JsBnot(inner) => ExpressionDesc::JsBnot(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::Seq(left, right) => ExpressionDesc::Seq(
            Box::new(flatten_and_mark_dead_expression(
                *left,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *right,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::Cond(test, consequent, alternate) => ExpressionDesc::Cond(
            Box::new(flatten_and_mark_dead_expression(
                *test,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *consequent,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *alternate,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::Bin(op, left, right) => ExpressionDesc::Bin(
            op,
            Box::new(flatten_and_mark_dead_expression(
                *left,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *right,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::FlatCall(func, args) => ExpressionDesc::FlatCall(
            Box::new(flatten_and_mark_dead_expression(
                *func,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *args,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(flatten_and_mark_dead_expression(
                *func,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            args.into_iter()
                .map(|arg| {
                    flatten_and_mark_dead_expression(arg, id_gen, substitution, jsx_preserve)
                })
                .collect(),
            info,
        ),
        ExpressionDesc::ArrayIndex(left, right) => {
            let left = flatten_and_mark_dead_expression(*left, id_gen, substitution, jsx_preserve);
            let right =
                flatten_and_mark_dead_expression(*right, id_gen, substitution, jsx_preserve);
            if let Some(rewritten) =
                direct_projection_from_pure_literal(&left, None, int_literal(&right))
            {
                return rewritten;
            }
            ExpressionDesc::ArrayIndex(Box::new(left), Box::new(right))
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(flatten_and_mark_dead_expression(
                *tag,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            strings,
            values
                .into_iter()
                .map(|value| {
                    flatten_and_mark_dead_expression(value, id_gen, substitution, jsx_preserve)
                })
                .collect(),
        ),
        ExpressionDesc::InterpolatedTemplate { segments, values } => {
            ExpressionDesc::InterpolatedTemplate {
                segments,
                values: values
                    .into_iter()
                    .map(|value| {
                        flatten_and_mark_dead_expression(value, id_gen, substitution, jsx_preserve)
                    })
                    .collect(),
            }
        }
        ExpressionDesc::StaticIndex(target, field, pos) => {
            let target =
                flatten_and_mark_dead_expression(*target, id_gen, substitution, jsx_preserve);
            if let Some(rewritten) = direct_projection_from_pure_literal(&target, Some(&field), pos)
            {
                return rewritten;
            }
            ExpressionDesc::StaticIndex(Box::new(target), field, pos)
        }
        ExpressionDesc::New(target, args) => ExpressionDesc::New(
            Box::new(flatten_and_mark_dead_expression(
                *target,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            args.map(|items| {
                items
                    .into_iter()
                    .map(|arg| {
                        flatten_and_mark_dead_expression(arg, id_gen, substitution, jsx_preserve)
                    })
                    .collect()
            }),
        ),
        ExpressionDesc::Var(var) => ExpressionDesc::Var(var),
        ExpressionDesc::Fun {
            is_method,
            params,
            body,
            env,
            return_unit,
            async_,
            directive,
        } => ExpressionDesc::Fun {
            is_method,
            params,
            body: flatten_and_mark_dead_block(body, id_gen, substitution, jsx_preserve),
            env,
            return_unit,
            async_,
            directive,
        },
        ExpressionDesc::Str(txt) => ExpressionDesc::Str(txt),
        ExpressionDesc::TemplateLiteral(segment) => ExpressionDesc::TemplateLiteral(segment),
        ExpressionDesc::JsonLiteral(source) => ExpressionDesc::JsonLiteral(source),
        ExpressionDesc::RawJsCode(info) => ExpressionDesc::RawJsCode(info),
        ExpressionDesc::Array(items, mutable_flag) => ExpressionDesc::Array(
            items
                .into_iter()
                .map(|item| {
                    flatten_and_mark_dead_expression(item, id_gen, substitution, jsx_preserve)
                })
                .collect(),
            mutable_flag,
        ),
        ExpressionDesc::OptionalBlock(inner, flag) => ExpressionDesc::OptionalBlock(
            Box::new(flatten_and_mark_dead_expression(
                *inner,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            flag,
        ),
        ExpressionDesc::CamlBlock(items, mutable_flag, tag_info) => ExpressionDesc::CamlBlock(
            items
                .into_iter()
                .map(|item| {
                    flatten_and_mark_dead_expression(item, id_gen, substitution, jsx_preserve)
                })
                .collect(),
            mutable_flag,
            tag_info,
        ),
        ExpressionDesc::CamlBlockTag(inner, tag) => ExpressionDesc::CamlBlockTag(
            Box::new(flatten_and_mark_dead_expression(
                *inner,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            tag,
        ),
        ExpressionDesc::Number(number) => ExpressionDesc::Number(number),
        // In JSX preserve mode, keep a JSX tag like `M.make` as it is: the
        // field's value may be a variable with a lowercase name, which JSX
        // reads as an intrinsic element, so the printer would have to print
        // the call instead (#7432).
        ExpressionDesc::Jsx(jsx)
            if jsx_preserve
                && matches!(
                    jsx.tag.desc,
                    ExpressionDesc::StaticIndex(..) | ExpressionDesc::ArrayIndex(..)
                ) =>
        {
            let mut jsx = *jsx;
            let tag = std::mem::replace(&mut jsx.tag, Expression::undefined(false));
            let mut jsx = jsx.map(|value| {
                flatten_and_mark_dead_expression(value, id_gen, substitution, jsx_preserve)
            });
            jsx.tag = tag;
            ExpressionDesc::Jsx(Box::new(jsx))
        }
        ExpressionDesc::Jsx(jsx) => ExpressionDesc::Jsx(Box::new(jsx.map(|value| {
            flatten_and_mark_dead_expression(value, id_gen, substitution, jsx_preserve)
        }))),
        ExpressionDesc::Object(entries) => ExpressionDesc::Object(
            entries
                .into_iter()
                .map(|entry| {
                    entry.map(|value| {
                        flatten_and_mark_dead_expression(value, id_gen, substitution, jsx_preserve)
                    })
                })
                .collect(),
        ),
        ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit },
        ExpressionDesc::Null => ExpressionDesc::Null,
        ExpressionDesc::Await(inner) => ExpressionDesc::Await(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::Spread(inner) => ExpressionDesc::Spread(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::RecordRest(fields, source) => ExpressionDesc::RecordRest(
            fields,
            Box::new(flatten_and_mark_dead_expression(
                *source,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
    };

    Expression {
        source_loc,
        desc,
        comment,
    }
}

fn try_substitute_caml_block_projection(
    expr: &Expression,
    substitution: &HashMap<Ident, Expression>,
) -> Option<Expression> {
    match &expr.desc {
        ExpressionDesc::ArrayIndex(left, right) => {
            let ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) = &left.desc else {
                return None;
            };
            let ExpressionDesc::Number(Number::Int { i, .. }) = right.desc else {
                return None;
            };
            substituted_caml_block_item(substitution, id, None, i)
        }
        ExpressionDesc::StaticIndex(target, field, Some(index)) => {
            let ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) = &target.desc else {
                return None;
            };
            substituted_caml_block_item(substitution, id, Some(field), *index)
        }
        _ => None,
    }
}

fn substituted_caml_block_item(
    substitution: &HashMap<Ident, Expression>,
    id: &Ident,
    field: Option<&str>,
    index: i32,
) -> Option<Expression> {
    let expression = substitution.get(id)?;
    let substitutable = is_simple_substituted_index_value;
    let ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, tag_info) = &expression.desc
    else {
        return None;
    };
    if let Some(field) = field {
        match &**tag_info {
            TagInfo::Record { fields, .. } | TagInfo::RecordInlined { fields, .. } => {
                let item = items
                    .iter()
                    .zip(fields.iter())
                    .find_map(|(item, (field_name, _))| (field_name == field).then_some(item))?;
                return substitutable(item).then(|| item.clone());
            }
            _ => {}
        }
    }
    let item = items.get(usize::try_from(index).ok()?)?;
    substitutable(item).then(|| item.clone())
}

fn should_materialize_block_binding_items(
    property: LetKind,
    items: &[Expression],
    tag_info: &TagInfo,
) -> bool {
    // OCaml's substitution pass matches every immutable `Caml_block`
    // with at least two elements, including `Blk_poly_var`, before
    // splitting complex payload fields
    // (`compiler/core/js_pass_flatten_and_mark_dead.ml:174-221`).
    let item_count = match tag_info {
        TagInfo::Record { .. } | TagInfo::RecordInlined { .. } => tag_info.logical_field_count(),
        _ => items.len(),
    };
    if item_count < 2 {
        return false;
    }

    // Checked-in OCaml snapshots keep alias-bound deep constants inline, while
    // still materializing Strict/StrictOpt bindings and alias blocks with
    // computed payloads.
    !(property == LetKind::Alias && items.iter().all(is_deep_constant_block_binding_item))
}

fn is_deep_constant_block_binding_item(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Number(_)
        | ExpressionDesc::Str(_)
        | ExpressionDesc::TemplateLiteral(_)
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Undefined { .. } => true,
        ExpressionDesc::OptionalBlock(inner, _) => is_deep_constant_block_binding_item(inner),
        ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _) => {
            items.iter().all(is_deep_constant_block_binding_item)
        }
        _ => false,
    }
}

fn is_simple_block_binding_item(expr: &Expression) -> bool {
    // Mirror OCaml's `js_pass_flatten_and_mark_dead.ml:188-193` "simple"
    // case: only `Var`, `Number`, `Str`, `Bool`, `Undefined` items stay
    // inline; everything else, including `Optional_block` and any
    // `Caml_block`, is hoisted into a fresh local binding. `Lconst
    // Const_block` materializes as `Caml_block(NA, ...)` (see
    // `Self::compile_constant`) so it intentionally does NOT match
    // `Caml_block(Immutable, ...)` patterns elsewhere — and therefore does
    // NOT count as simple here either.
    matches!(
        &expr.desc,
        ExpressionDesc::Var(_)
            | ExpressionDesc::Number(_)
            | ExpressionDesc::Str(_)
            | ExpressionDesc::TemplateLiteral(_)
            | ExpressionDesc::Bool(_)
            | ExpressionDesc::Undefined { .. }
    )
}

fn is_simple_substituted_index_value(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Var(_)
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Str(_)
        | ExpressionDesc::TemplateLiteral(_)
        | ExpressionDesc::Undefined { .. } => true,
        ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, tag)
            if matches!(**tag, TagInfo::Constructor { .. }) =>
        {
            items.iter().all(is_simple_substituted_index_value)
        }
        _ => false,
    }
}

fn block_substitution_name(ident: &Ident, tag_info: &TagInfo, index: usize) -> String {
    let suffix = match tag_info {
        TagInfo::Module(fields) => fields
            .get(index)
            .cloned()
            .unwrap_or_else(|| index.to_string()),
        TagInfo::Record { fields, .. } => fields
            .get(index)
            .map(|(field, _)| field.clone())
            .unwrap_or_else(|| index.to_string()),
        _ => index.to_string(),
    };
    format!("{}_{}", ident.name(), suffix)
}

pub(crate) fn max_ident_stamp_in_program(program: &Program) -> i32 {
    program.exports.iter().fold(
        max_ident_stamp_in_block(&program.block),
        |max_stamp, export| max_stamp.max(export.stamp()),
    )
}

#[derive(Debug, Clone, Copy)]
enum MarkDeadInfo {
    Recursive,
    Info {
        pure: bool,
        used: bool,
        exported: bool,
    },
}

fn mark_dead_code(program: &mut Program) {
    let mut states = HashMap::new();
    collect_mark_dead_states_block(&program.block, &program.export_set, &mut states);
    apply_mark_dead_states_block(&mut program.block, &states);
}

fn collect_mark_dead_states_block(
    block: &Block,
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    for stmt in block {
        collect_mark_dead_states_statement(stmt, export_set, states);
    }
}

fn collect_mark_dead_states_statement(
    stmt: &Statement,
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    match &stmt.desc {
        StatementDesc::Block(block) => collect_mark_dead_states_block(block, export_set, states),
        StatementDesc::Variable(decl) => {
            collect_mark_dead_states_variable(decl, export_set, states)
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            collect_mark_dead_states_expression(expr, states);
        }
        StatementDesc::If(cond, then_block, else_block) => {
            collect_mark_dead_states_expression(cond, states);
            collect_mark_dead_states_block(then_block, export_set, states);
            collect_mark_dead_states_block(else_block, export_set, states);
        }
        StatementDesc::While(_, cond, body) => {
            collect_mark_dead_states_expression(cond, states);
            collect_mark_dead_states_block(body, export_set, states);
        }
        StatementDesc::ForRange(_, start, finish, _, _, body) => {
            if let Some(start) = start {
                collect_mark_dead_states_expression(start, states);
            }
            collect_mark_dead_states_expression(finish, states);
            collect_mark_dead_states_block(body, export_set, states);
        }
        StatementDesc::ForOf(_, _, iterable, body)
        | StatementDesc::ForAwaitOf(_, _, iterable, body) => {
            collect_mark_dead_states_expression(iterable, states);
            collect_mark_dead_states_block(body, export_set, states);
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            collect_mark_dead_states_expression(test, states);
            for (_, clause) in clauses {
                collect_mark_dead_states_block(&clause.body, export_set, states);
            }
            if let Some(default) = default {
                collect_mark_dead_states_block(default, export_set, states);
            }
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            collect_mark_dead_states_expression(test, states);
            for clause in clauses {
                collect_mark_dead_states_block(&clause.clause.body, export_set, states);
            }
            if let Some(default) = default {
                collect_mark_dead_states_block(default, export_set, states);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            collect_mark_dead_states_block(body, export_set, states);
            if let Some((_, block)) = catch {
                collect_mark_dead_states_block(block, export_set, states);
            }
            if let Some(block) = finally {
                collect_mark_dead_states_block(block, export_set, states);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break(_) | StatementDesc::Continue(_) => {}
    }
}

fn collect_mark_dead_states_variable(
    decl: &VariableDeclaration,
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    match decl.ident_info.used_stats {
        UsedStats::DeadPure => return,
        UsedStats::DeadNonPure => {
            if let Some(value) = &decl.value {
                collect_mark_dead_states_expression(value, states);
            }
            return;
        }
        _ => {}
    }

    let pure = match &decl.value {
        None => true,
        Some(value) => {
            collect_mark_dead_states_expression(value, states);
            js_expr_no_side_effects(value)
        }
    };
    let exported = export_set.contains(&decl.ident);
    match states.get(&decl.ident).copied() {
        Some(MarkDeadInfo::Recursive) => {
            states.insert(
                decl.ident,
                MarkDeadInfo::Info {
                    pure,
                    used: true,
                    exported,
                },
            );
        }
        Some(MarkDeadInfo::Info { .. }) => {}
        None => {
            states.insert(
                decl.ident,
                MarkDeadInfo::Info {
                    pure,
                    used: false,
                    exported,
                },
            );
        }
    }
}

fn collect_mark_dead_states_expression(
    expr: &Expression,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) => mark_dead_ident_use(id, states),
        ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(_, _))
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str(_)
        | ExpressionDesc::TemplateLiteral(_)
        | ExpressionDesc::JsonLiteral(_)
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_) => {}
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::RecordRest(_, inner) => {
            collect_mark_dead_states_expression(inner, states)
        }
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            collect_mark_dead_states_expression(left, states);
            collect_mark_dead_states_expression(right, states);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            collect_mark_dead_states_expression(test, states);
            collect_mark_dead_states_expression(consequent, states);
            collect_mark_dead_states_expression(alternate, states);
        }
        ExpressionDesc::Call(func, args, _) => {
            collect_mark_dead_states_expression(func, states);
            for arg in args {
                collect_mark_dead_states_expression(arg, states);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, _, values) => {
            collect_mark_dead_states_expression(tag, states);
            for value in values {
                collect_mark_dead_states_expression(value, states);
            }
        }
        ExpressionDesc::InterpolatedTemplate { values, .. } => {
            for value in values {
                collect_mark_dead_states_expression(value, states);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => {
            collect_mark_dead_states_expression(target, states)
        }
        ExpressionDesc::New(target, args) => {
            collect_mark_dead_states_expression(target, states);
            if let Some(args) = args {
                for arg in args {
                    collect_mark_dead_states_expression(arg, states);
                }
            }
        }
        ExpressionDesc::Fun { body, .. } => {
            for stmt in body {
                collect_mark_dead_states_statement(stmt, &HashSet::new(), states);
            }
        }
        ExpressionDesc::Array(items, _) => {
            for item in items {
                collect_mark_dead_states_expression(item, states);
            }
        }
        ExpressionDesc::CamlBlock(items, _, _) => {
            for item in items {
                collect_mark_dead_states_expression(item, states);
            }
        }
        ExpressionDesc::Jsx(jsx) => {
            for value in jsx.expressions() {
                collect_mark_dead_states_expression(value, states);
            }
        }
        ExpressionDesc::Object(entries) => {
            for entry in entries {
                collect_mark_dead_states_expression(entry.expression(), states);
            }
        }
    }
}

fn mark_dead_ident_use(id: &Ident, states: &mut HashMap<Ident, MarkDeadInfo>) {
    match states.get_mut(id) {
        None => {
            states.insert(*id, MarkDeadInfo::Recursive);
        }
        Some(MarkDeadInfo::Recursive) => {}
        Some(MarkDeadInfo::Info { used, .. }) => {
            *used = true;
        }
    }
}

fn apply_mark_dead_states_block(block: &mut Block, states: &HashMap<Ident, MarkDeadInfo>) {
    for stmt in block {
        apply_mark_dead_states_statement(stmt, states);
    }
}

fn apply_mark_dead_states_statement(stmt: &mut Statement, states: &HashMap<Ident, MarkDeadInfo>) {
    match &mut stmt.desc {
        StatementDesc::Block(block) => apply_mark_dead_states_block(block, states),
        StatementDesc::Variable(decl) => {
            apply_mark_dead_states_variable(decl, states);
            if let Some(value) = &mut decl.value {
                apply_mark_dead_states_expression(value, states);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            apply_mark_dead_states_expression(expr, states);
        }
        StatementDesc::If(_, then_block, else_block) => {
            apply_mark_dead_states_block(then_block, states);
            apply_mark_dead_states_block(else_block, states);
        }
        StatementDesc::While(_, _, body) => apply_mark_dead_states_block(body, states),
        StatementDesc::ForRange(_, _, _, _, _, body) => apply_mark_dead_states_block(body, states),
        StatementDesc::ForOf(_, _, _, body) | StatementDesc::ForAwaitOf(_, _, _, body) => {
            apply_mark_dead_states_block(body, states)
        }
        StatementDesc::IntSwitch(_, clauses, default) => {
            for (_, clause) in clauses {
                apply_mark_dead_states_block(&mut clause.body, states);
            }
            if let Some(default) = default {
                apply_mark_dead_states_block(default, states);
            }
        }
        StatementDesc::StringSwitch(_, clauses, default) => {
            for clause in clauses {
                apply_mark_dead_states_block(&mut clause.clause.body, states);
            }
            if let Some(default) = default {
                apply_mark_dead_states_block(default, states);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            apply_mark_dead_states_block(body, states);
            if let Some((_, block)) = catch {
                apply_mark_dead_states_block(block, states);
            }
            if let Some(block) = finally {
                apply_mark_dead_states_block(block, states);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break(_) | StatementDesc::Continue(_) => {}
    }
}

fn apply_mark_dead_states_variable(
    decl: &mut VariableDeclaration,
    states: &HashMap<Ident, MarkDeadInfo>,
) {
    let Some(MarkDeadInfo::Info {
        pure,
        used,
        exported,
    }) = states.get(&decl.ident).copied()
    else {
        return;
    };

    let status = if exported {
        UsedStats::Exported
    } else if used {
        UsedStats::Used
    } else if pure {
        UsedStats::DeadPure
    } else {
        UsedStats::DeadNonPure
    };
    update_used_stats(&mut decl.ident_info, status);
}

fn apply_mark_dead_states_expression(expr: &mut Expression, states: &HashMap<Ident, MarkDeadInfo>) {
    match &mut expr.desc {
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::RecordRest(_, inner) => apply_mark_dead_states_expression(inner, states),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            apply_mark_dead_states_expression(left, states);
            apply_mark_dead_states_expression(right, states);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            apply_mark_dead_states_expression(test, states);
            apply_mark_dead_states_expression(consequent, states);
            apply_mark_dead_states_expression(alternate, states);
        }
        ExpressionDesc::Call(func, args, _) => {
            apply_mark_dead_states_expression(func, states);
            for arg in args {
                apply_mark_dead_states_expression(arg, states);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, _, values) => {
            apply_mark_dead_states_expression(tag, states);
            for value in values {
                apply_mark_dead_states_expression(value, states);
            }
        }
        ExpressionDesc::InterpolatedTemplate { values, .. } => {
            for value in values {
                apply_mark_dead_states_expression(value, states);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => {
            apply_mark_dead_states_expression(target, states)
        }
        ExpressionDesc::New(target, args) => {
            apply_mark_dead_states_expression(target, states);
            if let Some(args) = args {
                for arg in args {
                    apply_mark_dead_states_expression(arg, states);
                }
            }
        }
        ExpressionDesc::Fun { body, .. } => apply_mark_dead_states_block(body, states),
        ExpressionDesc::Array(items, _) => {
            for item in items {
                apply_mark_dead_states_expression(item, states);
            }
        }
        ExpressionDesc::CamlBlock(items, _, _) => {
            for item in items {
                apply_mark_dead_states_expression(item, states);
            }
        }
        ExpressionDesc::Jsx(jsx) => {
            for value in jsx.expressions_mut() {
                apply_mark_dead_states_expression(value, states);
            }
        }
        ExpressionDesc::Object(entries) => {
            for entry in entries {
                apply_mark_dead_states_expression(entry.expression_mut(), states);
            }
        }
        ExpressionDesc::Var(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str(_)
        | ExpressionDesc::TemplateLiteral(_)
        | ExpressionDesc::JsonLiteral(_)
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_) => {}
    }
}

fn update_used_stats(info: &mut IdentInfo, status: UsedStats) {
    if matches!(
        info.used_stats,
        UsedStats::DeadPure | UsedStats::DeadNonPure | UsedStats::Exported
    ) {
        return;
    }
    info.used_stats = status;
}

fn flatten_program(mut program: Program) -> Program {
    program.block = flatten_block(program.block);
    program
}

fn flatten_block(block: Block) -> Block {
    let mut flattened = Vec::new();

    for stmt in block {
        match flatten_statement(stmt) {
            Statement {
                desc: StatementDesc::Block(inner),
                ..
            } => flattened.extend(inner),
            other => flattened.push(other),
        }
    }

    flattened
}

fn flatten_statement(stmt: Statement) -> Statement {
    let Statement {
        source_loc,
        desc,
        comment,
    } = stmt;

    match desc {
        StatementDesc::Exp(expr) => {
            let Expression {
                source_loc: expr_loc,
                desc,
                comment: expr_comment,
            } = expr;

            match desc {
                ExpressionDesc::Seq(_, _) => {
                    let block = flatten_sequence_statements(Expression {
                        source_loc: expr_loc,
                        desc,
                        comment: expr_comment,
                    });
                    // OCaml uses `S.block` here, not a raw `Block`
                    // (compiler/core/js_pass_flatten.ml:43-47), so a single
                    // empty flattened effect is normalized before printing.
                    Statement::block(block)
                }
                ExpressionDesc::CamlBlock(args, _, _) => {
                    let block = args
                        .into_iter()
                        .map(|arg| flatten_statement(Statement::exp(arg)))
                        .collect();
                    // OCaml's Caml_block flattening also goes through
                    // `S.block` (compiler/core/js_pass_flatten.ml:48-53).
                    Statement::block(block)
                }
                ExpressionDesc::Cond(test, consequent, alternate) => {
                    // OCaml keeps the conditional predicate untouched here;
                    // only the consequent/alternate are re-entered as
                    // statements (compiler/core/js_pass_flatten.ml).
                    // Re-flattening `test` eagerly expands nested callback
                    // bodies inside large conditions before later passes see
                    // the same shape OCaml preserves. A branch whose value is
                    // pure leaves nothing to run.
                    let branch = |e: Expression| {
                        if crate::js_ir::expression_has_no_side_effects(&e) {
                            vec![]
                        } else {
                            vec![flatten_statement(Statement::exp(e))]
                        }
                    };
                    let ifso = branch(*consequent);
                    let ifnot = branch(*alternate);
                    let desc = match (ifso.is_empty(), ifnot.is_empty()) {
                        (true, true) => {
                            if crate::js_ir::expression_has_no_side_effects(&test) {
                                StatementDesc::Block(vec![])
                            } else {
                                StatementDesc::Exp(*test)
                            }
                        }
                        (true, false) => StatementDesc::If(Expression::not(*test), ifnot, vec![]),
                        (false, _) => StatementDesc::If(*test, ifso, ifnot),
                    };
                    Statement {
                        // js_pass_flatten.ml takes the condition expression's
                        // `source_loc`.
                        source_loc: expr_loc,
                        desc,
                        comment,
                    }
                }
                ExpressionDesc::Bin(BinOp::Eq, target, value) => {
                    if matches!(value.desc, ExpressionDesc::Seq(_, _)) {
                        let mut exprs = Vec::new();
                        flatten_sequence_expressions(*value, &mut exprs);
                        let last = exprs
                            .pop()
                            .expect("sequence flattening must produce at least one expression");
                        let mut block: Block = exprs
                            .into_iter()
                            .map(|expr| flatten_statement(Statement::exp(expr)))
                            .collect();
                        block.push(flatten_statement(Statement::exp(Expression::bin(
                            BinOp::Eq,
                            *target,
                            last,
                        ))));
                        // Match OCaml's `S.block` in
                        // compiler/core/js_pass_flatten.ml:63-77.
                        Statement::block(block)
                    } else {
                        Statement {
                            source_loc,
                            desc: StatementDesc::Exp(flatten_expression(Expression {
                                source_loc: expr_loc,
                                desc: ExpressionDesc::Bin(BinOp::Eq, target, value),
                                comment: expr_comment,
                            })),
                            comment,
                        }
                    }
                }
                desc => Statement {
                    source_loc,
                    desc: StatementDesc::Exp(flatten_expression(Expression {
                        source_loc: expr_loc,
                        desc,
                        comment: expr_comment,
                    })),
                    comment,
                },
            }
        }
        StatementDesc::Return(expr) => {
            let Expression {
                source_loc: expr_loc,
                desc,
                comment: expr_comment,
            } = expr;

            match desc {
                ExpressionDesc::Cond(test, consequent, alternate) => Statement {
                    // js_pass_flatten.ml:54-61 / 79-86 take the condition
                    // expression's `source_loc`.
                    source_loc: expr_loc,
                    // Same predicate preservation as OCaml's Return(Cond)
                    // flatten arm (compiler/core/js_pass_flatten.ml:79-86).
                    desc: StatementDesc::If(
                        *test,
                        vec![flatten_statement(Statement::return_(*consequent))],
                        vec![flatten_statement(Statement::return_(*alternate))],
                    ),
                    comment,
                },
                ExpressionDesc::Seq(_, _) => {
                    let mut exprs = Vec::new();
                    flatten_sequence_expressions(
                        Expression {
                            source_loc: expr_loc,
                            desc,
                            comment: expr_comment,
                        },
                        &mut exprs,
                    );
                    let last = exprs
                        .pop()
                        .expect("return sequence flattening must produce at least one expression");
                    let mut block: Block = exprs
                        .into_iter()
                        .map(|expr| flatten_statement(Statement::exp(expr)))
                        .collect();
                    block.push(flatten_statement(Statement::return_(last)));
                    // OCaml wraps the flattened return sequence with
                    // `S.block` before applying `super.statement`
                    // (compiler/core/js_pass_flatten.ml:88-96).
                    Statement::block(block)
                }
                desc => Statement {
                    source_loc,
                    desc: StatementDesc::Return(flatten_expression(Expression {
                        source_loc: expr_loc,
                        desc,
                        comment: expr_comment,
                    })),
                    comment,
                },
            }
        }
        StatementDesc::Block(block) => {
            if block.len() == 1 {
                flatten_statement(block.into_iter().next().expect("single-item block"))
            } else {
                Statement {
                    source_loc,
                    desc: StatementDesc::Block(flatten_block(block)),
                    comment,
                }
            }
        }
        StatementDesc::Variable(decl) => Statement {
            source_loc,
            desc: StatementDesc::Variable(VariableDeclaration {
                ident: decl.ident,
                value: decl.value.map(flatten_expression),
                property: decl.property,
                ident_info: decl.ident_info,
            }),
            comment,
        },
        StatementDesc::If(cond, then_block, else_block) => Statement {
            source_loc,
            desc: StatementDesc::If(
                flatten_expression(cond),
                flatten_block(then_block),
                flatten_block(else_block),
            ),
            comment,
        },
        StatementDesc::While(label, cond, body) => Statement {
            source_loc,
            desc: StatementDesc::While(label, flatten_expression(cond), flatten_block(body)),
            comment,
        },
        StatementDesc::ForRange(label, start, finish, ident, direction, body) => Statement {
            source_loc,
            desc: StatementDesc::ForRange(
                label,
                start.map(|expr| Box::new(flatten_expression(*expr))),
                Box::new(flatten_expression(*finish)),
                ident,
                direction,
                flatten_block(body),
            ),
            comment,
        },
        StatementDesc::ForOf(label, ident, iterable, body) => Statement {
            source_loc,
            desc: StatementDesc::ForOf(
                label,
                ident,
                Box::new(flatten_expression(*iterable)),
                flatten_block(body),
            ),
            comment,
        },
        StatementDesc::ForAwaitOf(label, ident, iterable, body) => Statement {
            source_loc,
            desc: StatementDesc::ForAwaitOf(
                label,
                ident,
                Box::new(flatten_expression(*iterable)),
                flatten_block(body),
            ),
            comment,
        },
        StatementDesc::IntSwitch(test, clauses, default) => Statement {
            source_loc,
            desc: StatementDesc::IntSwitch(
                flatten_expression(test),
                clauses
                    .into_iter()
                    .map(|(tag, clause)| (tag, flatten_case_clause(clause)))
                    .collect(),
                default.map(flatten_block),
            ),
            comment,
        },
        StatementDesc::StringSwitch(test, clauses, default) => Statement {
            source_loc,
            desc: StatementDesc::StringSwitch(
                flatten_expression(test),
                clauses
                    .into_iter()
                    .map(|clause| StringClause {
                        tag_type: clause.tag_type,
                        clause: flatten_case_clause(clause.clause),
                    })
                    .collect(),
                default.map(flatten_block),
            ),
            comment,
        },
        StatementDesc::Throw(expr) => Statement {
            source_loc,
            desc: StatementDesc::Throw(flatten_expression(expr)),
            comment,
        },
        StatementDesc::Try(body, catch, finally) => Statement {
            source_loc,
            desc: StatementDesc::Try(
                flatten_block(body),
                catch.map(|(id, block)| (id, flatten_block(block))),
                finally.map(flatten_block),
            ),
            comment,
        },
        StatementDesc::Debugger => Statement {
            source_loc,
            desc: StatementDesc::Debugger,
            comment,
        },
        StatementDesc::Break(label) => Statement {
            source_loc,
            desc: StatementDesc::Break(label),
            comment,
        },
        StatementDesc::Continue(label) => Statement {
            source_loc,
            desc: StatementDesc::Continue(label),
            comment,
        },
    }
}

fn flatten_case_clause(clause: CaseClause) -> CaseClause {
    CaseClause {
        source_loc: clause.source_loc,
        body: flatten_block(clause.body),
        should_break: clause.should_break,
        comment: clause.comment,
    }
}

fn flatten_expression(expr: Expression) -> Expression {
    let source_loc = expr.source_loc;
    let comment = expr.comment;
    let desc = match expr.desc {
        ExpressionDesc::Length(inner, object) => {
            ExpressionDesc::Length(Box::new(flatten_expression(*inner)), object)
        }
        ExpressionDesc::IsNullOrUndefined(inner) => {
            ExpressionDesc::IsNullOrUndefined(Box::new(flatten_expression(*inner)))
        }
        ExpressionDesc::StringAppend(left, right) => ExpressionDesc::StringAppend(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::Bool(value) => ExpressionDesc::Bool(value),
        ExpressionDesc::Typeof(inner) => {
            ExpressionDesc::Typeof(Box::new(flatten_expression(*inner)))
        }
        ExpressionDesc::In(left, right) => ExpressionDesc::In(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::JsNot(inner) => ExpressionDesc::JsNot(Box::new(flatten_expression(*inner))),
        ExpressionDesc::JsBnot(inner) => {
            ExpressionDesc::JsBnot(Box::new(flatten_expression(*inner)))
        }
        ExpressionDesc::Seq(left, right) => ExpressionDesc::Seq(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::Cond(test, consequent, alternate) => ExpressionDesc::Cond(
            Box::new(flatten_expression(*test)),
            Box::new(flatten_expression(*consequent)),
            Box::new(flatten_expression(*alternate)),
        ),
        ExpressionDesc::Bin(op, left, right) => ExpressionDesc::Bin(
            op,
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::FlatCall(func, args) => ExpressionDesc::FlatCall(
            Box::new(flatten_expression(*func)),
            Box::new(flatten_expression(*args)),
        ),
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(flatten_expression(*func)),
            args.into_iter().map(flatten_expression).collect(),
            info,
        ),
        ExpressionDesc::ArrayIndex(left, right) => ExpressionDesc::ArrayIndex(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::TaggedTemplate(tag, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(flatten_expression(*tag)),
            strings,
            values.into_iter().map(flatten_expression).collect(),
        ),
        ExpressionDesc::InterpolatedTemplate { segments, values } => {
            ExpressionDesc::InterpolatedTemplate {
                segments,
                values: values.into_iter().map(flatten_expression).collect(),
            }
        }
        ExpressionDesc::StaticIndex(target, field, pos) => {
            ExpressionDesc::StaticIndex(Box::new(flatten_expression(*target)), field, pos)
        }
        ExpressionDesc::New(target, args) => ExpressionDesc::New(
            Box::new(flatten_expression(*target)),
            args.map(|args| args.into_iter().map(flatten_expression).collect()),
        ),
        ExpressionDesc::Var(var) => ExpressionDesc::Var(var),
        ExpressionDesc::Fun {
            is_method,
            params,
            body,
            env,
            return_unit,
            async_,
            directive,
        } => ExpressionDesc::Fun {
            is_method,
            params,
            body: flatten_block(body),
            env,
            return_unit,
            async_,
            directive,
        },
        ExpressionDesc::Str(txt) => ExpressionDesc::Str(txt),
        ExpressionDesc::TemplateLiteral(segment) => ExpressionDesc::TemplateLiteral(segment),
        ExpressionDesc::JsonLiteral(source) => ExpressionDesc::JsonLiteral(source),
        ExpressionDesc::RawJsCode(info) => ExpressionDesc::RawJsCode(info),
        ExpressionDesc::Array(items, mutable_flag) => ExpressionDesc::Array(
            items.into_iter().map(flatten_expression).collect(),
            mutable_flag,
        ),
        ExpressionDesc::OptionalBlock(inner, flag) => {
            ExpressionDesc::OptionalBlock(Box::new(flatten_expression(*inner)), flag)
        }
        ExpressionDesc::CamlBlock(items, mutable_flag, tag_info) => ExpressionDesc::CamlBlock(
            items.into_iter().map(flatten_expression).collect(),
            mutable_flag,
            tag_info,
        ),
        ExpressionDesc::CamlBlockTag(inner, tag) => {
            ExpressionDesc::CamlBlockTag(Box::new(flatten_expression(*inner)), tag)
        }
        ExpressionDesc::Number(number) => ExpressionDesc::Number(number),
        ExpressionDesc::Jsx(jsx) => ExpressionDesc::Jsx(Box::new(jsx.map(flatten_expression))),
        ExpressionDesc::Object(entries) => ExpressionDesc::Object(
            entries
                .into_iter()
                .map(|entry| entry.map(flatten_expression))
                .collect(),
        ),
        ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit },
        ExpressionDesc::Null => ExpressionDesc::Null,
        ExpressionDesc::Await(inner) => ExpressionDesc::Await(Box::new(flatten_expression(*inner))),
        ExpressionDesc::Spread(inner) => {
            ExpressionDesc::Spread(Box::new(flatten_expression(*inner)))
        }
        ExpressionDesc::RecordRest(fields, source) => {
            ExpressionDesc::RecordRest(fields, Box::new(flatten_expression(*source)))
        }
    };

    Expression {
        source_loc,
        desc,
        comment,
    }
}

fn flatten_sequence_statements(expr: Expression) -> Block {
    let mut exprs = Vec::new();
    flatten_sequence_expressions(expr, &mut exprs);
    exprs
        .into_iter()
        .map(|expr| flatten_statement(Statement::exp(expr)))
        .collect()
}

fn flatten_sequence_expressions(expr: Expression, out: &mut Vec<Expression>) {
    let source_loc = expr.source_loc;
    match expr.desc {
        ExpressionDesc::Seq(left, right) => {
            flatten_sequence_expressions(*left, out);
            flatten_sequence_expressions(*right, out);
        }
        desc => out.push(Expression {
            source_loc,
            desc,
            comment: expr.comment,
        }),
    }
}
