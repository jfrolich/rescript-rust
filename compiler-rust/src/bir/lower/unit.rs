//! N1/K11: C:663 compile_deps_program_in_arena / C:1513 continues_toplevel_spine.
use super::*;

/// N1/K11: C:663 compile_deps_program_in_arena / C:1513 continues_toplevel_spine.
/// Consume top-level groups iteratively. No group in this slice creates loop
/// labels; loop-bearing groups remain Unsupported before label allocation.
pub(super) fn lower(
    input: super::super::bridge::Imported,
    locations: Option<&crate::lambda::LamLocTable>,
    direct: bool,
    resolver: Option<&crate::js_ir::ModulePathResolver>,
    cross_module_inline: bool,
    check_div_by_zero: bool,
) -> Result<Lowered, Unsupported> {
    let mut node = input.root;
    let mut state = State::new(input);
    state.direct = direct;
    state.resolver = resolver.cloned();
    state.cross_module_inline = cross_module_inline;
    state.check_div_by_zero = check_div_by_zero;
    state.locations = locations.cloned();
    if let Some(locations) = locations {
        state.located_functions = state
            .arena
            .pools
            .funcs
            .iter()
            .map(|f| {
                locations
                    .get(f.loc)
                    .is_some_and(|loc| !loc.loc_ghost && loc.loc_start.cnum >= 0)
            })
            .collect();
    }
    let mut accumulated: Option<Out> = None;
    loop {
        let view = state.source.view(node);
        let record_candidate = matches!(view, View::Let { value: Some(value), .. }
            if matches!(state.source.view(value), View::Prim { primitive, .. }
                if matches!(state.arena.primitive(primitive).primitive, crate::lambda::lam_primitive::Primitive::Pduprecord)));
        let (cx, group, next) = if record_candidate {
            (Cx::value(), node, None)
        } else if let View::Let { var, value, body } = view {
            state.source_steps += 1;
            let kind = match state.source.node(node).aux() & 3 {
                0 => LetKind::Strict,
                1 => LetKind::Alias,
                2 => LetKind::StrictOpt,
                3 => LetKind::Variable,
                _ => unreachable!("masked let kind"),
            };
            let Some(value) = value else {
                node = body;
                continue;
            };
            state.record_awaited_unit(var, value);
            (Cx::declare(kind, var), value, Some(body))
        } else if let View::Seq { first, second } = view {
            state.source_steps += 1;
            (Cx::effect(), first, Some(second))
        } else {
            (Cx::value(), node, None)
        };
        state.next_loop_label = 0;
        let probed = state.probe(cx, group)?;
        let mut out = state.realize(cx, probed);
        if next.is_some() {
            if let Some(value) = out.value.take() {
                state.drop_pure_effect(value);
                out.stmts = state.statements.since(Span { start: out.stmts.start, len: 0 });
            }
        }
        if out.finished == Finished::True {
            if let Some(next) = next {
                // C: compile_expr Let keeps the body's value after a finished
                // declaration. The shared export coercion still needs that block.
                let tail = state.probe(Cx::value(), next)?;
                let mut tail = state.realize(Cx::value(), tail);
                let value = if matches!(cx.cont, Cont::Declare(_, _)) { tail.value.take() } else { None };
                out = state.append_outputs(out, tail, None);
                out.value = value;
                if let Some(first) = accumulated.take() {
                    let value = out.value;
                    out = state.append_outputs(first, out, value);
                }
                return Ok(state.complete_unit(Probed::Out(out)));
            }
        }
        let value = out.value;
        let out = match accumulated.take() {
            Some(first) => state.append_outputs(first, out, value),
            None => out,
        };
        if let Some(next) = next {
            accumulated = Some(out);
            node = next;
        } else {
            return Ok(state.complete_unit(Probed::Out(out)));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::arena::LamArena;
    use crate::lambda::lam_compile::LambdaCompiler;
    use crate::lambda::lam_constant::Constant;
    use crate::lambda::lam_tag_info::TagInfo;

    #[test]
    fn supported_unit_exercises_both_texts_and_shared_export_coercion() {
        for exported in [false, true] {
            let mut source = LamArena::new();
            let names = if exported {
                vec![Ident::new("answer", 700, crate::ident::IdentFlags::NONE)]
            } else {
                vec![]
            };
            let values = if exported {
                vec![Constant::Int {
                    i: 42,
                    comment: None,
                }]
            } else {
                vec![]
            };
            let root = source.const_(Constant::Block {
                tag_info: Box::new(TagInfo::ModuleExport(names)),
                elements: values,
            });
            let mut compiler = LambdaCompiler::new();
            let (_, check) = compiler.compile_deps_program_with_lower_check::<true>(
                source,
                root,
                Default::default(),
            );
            let check = check.unwrap();
            assert!(matches!(
                check,
                crate::bir::shadow::LowerCheck::Supported(_)
            ));
            crate::bir::shadow::check_lower(check, "Exports.res", false).unwrap();
        }
    }

    #[test]
    fn top_level_groups_match_one_context_walk() {
        let mut source = LamArena::new();
        let id = Ident::new("binding", 10, crate::ident::IdentFlags::NONE);
        let value = source.const_(Constant::Int {
            i: 1,
            comment: None,
        });
        let head = source.const_(Constant::JsNull);
        let tail = source.var(id);
        let body = source.seq_raw(head, tail);
        let root = source.let_(LetKind::Strict, id, value, body);
        let input = crate::bir::bridge::import_lambda(&source, root).unwrap();
        let from_unit = lower(input, None, false, None, false, true).unwrap();
        let input = crate::bir::bridge::import_lambda(&source, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let probed = state.probe(Cx::value(), root).unwrap();
        let whole = state.complete_unit(probed);
        let print = |lowered: Lowered| {
            let p = crate::bir::bridge_j::export_js(&lowered.program).unwrap();
            crate::js_ir::print_deps_program_with_directives_and_options(
                &p,
                None,
                &[],
                false,
                false,
                false,
            )
        };
        assert_eq!(print(from_unit), print(whole));
    }
}
