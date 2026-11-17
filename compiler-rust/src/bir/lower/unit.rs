//! N1/K11: C:663 compile_deps_program_in_arena / C:1513 continues_toplevel_spine.
use super::*;
use super::js::Js as _;

/// N1/K11: C:663 compile_deps_program_in_arena / C:1513 continues_toplevel_spine.
/// Consume top-level groups iteratively. No group in this slice creates loop
/// labels; loop-bearing groups remain Unsupported before label allocation.
/// Cost: `State::new` (O(N + V + F + G), stated there); `resolver` and
/// `locations` are borrowed for the unit, O(1) and no allocation (a
/// header's location is read where its body is closed, `is_located`);
/// then one iteration per `Let` or `Seq` on the right spine of the unit
/// (one step each), which probes and realizes one top-level group
/// (`State::probe`, `State::realize`; the groups are disjoint subtrees)
/// and appends it (`append_outputs`); a finished declaration adds one
/// probe and realization of its body. Last, `complete_unit`.
pub(super) fn lower(
    input: super::super::bridge::ForLowering,
    locations: Option<&crate::lambda::LamLocTable>,
    direct: bool,
    resolver: Option<&crate::js_ir::ModulePathResolver>,
    cross_module_inline: bool,
    check_div_by_zero: bool,
    jsx_preserve: bool,
) -> Result<Lowered, Unsupported> {
    let input = input.into_imported();
    let mut node = input.root;
    let mut state = State::new(input);
    state.direct = direct;
    state.resolver = resolver;
    state.cross_module_inline = cross_module_inline;
    state.check_div_by_zero = check_div_by_zero;
    state.arena.js_scope.as_mut().expect("lowering scope").names.jsx_preserve = jsx_preserve;
    state.locations = locations;
    if locations.is_some() {
        state.source_functions = u32::try_from(state.arena.vars.funcs.len()).expect("function header count");
    }
    let mut accumulated: Option<Out<crate::bir::j::rows::Rows>> = None;
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
                state.drop_pure_effect(crate::bir::j::rows::Rows::node(value));
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
                    let value = out.value.take().map(crate::bir::j::rows::Rows::node);
                    out.value = value.map(crate::bir::j::rows::Rows::from_node);
                    out = state.append_outputs(first, out, value.map(crate::bir::j::rows::Rows::from_node));
                }
                return Ok(state.complete_unit(Probed::Out(out)));
            }
        }
        let mut out = out;
        let value = out.value.take().map(crate::bir::j::rows::Rows::node);
        out.value = value.map(crate::bir::j::rows::Rows::from_node);
        let value = value.map(crate::bir::j::rows::Rows::from_node);
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

    // Each count includes the operand stack of `Rows`, the implementation
    // of the lowering's interface, reserved once in `State::new`: the one
    // allocation the interface adds to a unit (THREE_TREES 11.4, "T6: the
    // interface" (a)).
    #[test]
    fn full_unit_allocation_boundary_conditionals() {
        assert_unit_allocation_count("conditionals", 86);
    }
    #[test]
    fn full_unit_allocation_boundary_switches() {
        assert_unit_allocation_count("switches", 103);
    }
    #[test]
    fn full_unit_allocation_boundary_applications() {
        assert_unit_allocation_count("applications", 86);
    }
    #[test]
    fn full_unit_allocation_boundary_untagged() {
        assert_unit_allocation_count("untagged", 156);
    }

    /// Import is outside measurement; fresh state construction, lowering,
    /// export coercion and owned completion are inside it. Warm the entry once
    /// per size, then pin the per-unit count, not zero bytes or zero allocations.
    fn assert_unit_allocation_count(shape: &str, expected: u64) {
        use crate::lambda::{LamLoc, ApInfo, ApplyStatus};
        use crate::lambda::lam_primitive::{Primitive as P, Mutable};
        use crate::lambda::{SwitchDispatch, SwitchKey};
        use crate::types::{VariantBlock, VariantBlockType, VariantConstructorCase as Case,
            VariantMatchingFacts, VariantTag};
        use crate::types::VariantLiteralTag as Literal;
        let mut counts = [0; 2];
        for (run, width) in [1_000, 10_000].into_iter().enumerate() {
            let mut a = LamArena::new();
            let x = Ident::new("x", 1, crate::ident::IdentFlags::NONE);
            let root = match shape {
                "conditionals" => {
                    let mut body = a.const_(Constant::Int { i: 0, comment: None });
                    for i in 1..=width {
                        let condition = a.var(x);
                        let yes = a.const_(Constant::Int { i, comment: None });
                        body = a.if_raw(condition, yes, body);
                    }
                    body
                }
                "applications" => {
                    let values: Vec<_> = (0..width).map(|_| {
                        let callee = a.var(x);
                        a.apply_raw(callee, &[], ApInfo { loc: LamLoc::NONE, status: ApplyStatus::Na })
                    }).collect();
                    a.prim_raw(P::Pmakearray, &values, LamLoc::NONE)
                }
                "switches" => {
                    let x = a.var(x);
                    let values: Vec<_> = (0..width).map(|i| a.const_(Constant::String(format!("value{i}")))).collect();
                    let values = a.add_list(&values);
                    let header = a.add_switch(true, (0..width).map(SwitchKey::Int), false, [], false, SwitchDispatch::Direct);
                    a.switch_raw(x, values, header)
                }
                "untagged" => {
                    let x = a.var(x);
                    let mut literals: Vec<_> = (0..width - 2).map(|i| Literal::String(format!("tag{i}"))).collect();
                    let keys: Vec<_> = literals.iter().enumerate().map(|(i, literal)|
                        SwitchKey::Constructor(Case::Constant(VariantTag {
                            name: crate::name::Name::new(&format!("C{i}")), literal: literal.clone(),
                        }))).collect();
                    literals.push(Literal::Int(42));
                    let kinds = vec![VariantBlockType::Number, VariantBlockType::Object];
                    let blocks: Vec<_> = kinds.iter().enumerate().map(|(i, kind)|
                        SwitchKey::Constructor(Case::Block(VariantBlock::Untagged {
                            tag: VariantTag { name: crate::name::Name::new(&format!("B{i}")), literal: Literal::String(format!("B{i}")) },
                            block_type: kind.clone(),
                        }))).collect();
                    let values: Vec<_> = (0..width + 1).map(|i| a.const_(Constant::String(format!("body{i}")))).collect();
                    let values = a.add_list(&values);
                    let header = a.add_switch(false, keys, false, blocks, true,
                        SwitchDispatch::Variant(VariantMatchingFacts { tag_name: None, literal_tags: literals, block_types: kinds }));
                    a.switch_raw(x, values, header)
                }
                _ => unreachable!(),
            };
            let export = Ident::new("answer", 2, crate::ident::IdentFlags::NONE);
            let root = a.prim_raw(P::Pmakeblock(TagInfo::ModuleExport(vec![export]), Mutable::Immutable), &[root], LamLoc::NONE);
            // Both imports are outside the interval. Each actual entry still
            // owns fresh state; process warmup cannot retain that state's pools.
            let warm = crate::bir::bridge::import_for_lowering(&a, root).0.unwrap();
            let input = crate::bir::bridge::import_for_lowering(&a, root).0.unwrap();
            let source_counts = input.storage_counts();
            let warm = super::super::lower_with_resolver(warm, None, true, None, false, true, false).unwrap();
            let visits = warm.switch_stats.source_visits;
            drop(warm);
            let mut result = None;
            let allocations = allocation_counter::measure(|| {
                allocation_window_start();
                result = Some(super::super::lower_with_resolver(input, None, true, None, false, true, false).unwrap());
                allocation_window_end();
            });
            let result = result.unwrap();
            assert_eq!(result.switch_stats.source_visits, visits);
            assert!(visits >= width as usize);
            assert_eq!(result.coerced.exports.len(), 1);
            result.program.arena.validate(Some(result.program.root)).unwrap();
            counts[run] = allocations.count_total;
            println!("full-unit {shape} width={width}: source={source_counts:?}, output_nodes={}, visits={visits}, {allocations:?}", result.program.arena.nodes.len());
        }
        assert_eq!(counts[0], counts[1], "{shape}: allocation count must not scale with visited nodes");
        // Release builds omit the debug-only child-uniqueness table.
        let expected = expected - u64::from(!cfg!(debug_assertions));
        assert_eq!(counts, [expected; 2], "{shape}: per-unit allocation budget changed");
    }

    /// The unit borrows the caller's location table and module resolver and
    /// reads a function header's location where its body is closed: lending
    /// a 10,000-row table and a resolver with 10,000 path overrides to a
    /// unit of 10,000 functions allocates exactly what lowering without them
    /// does, at 1,000 and at 10,000 of each. The functions' own locations
    /// are `NONE`, so the output is the same with and without the table.
    #[test]
    fn full_unit_borrows_locations_and_resolver() {
        use crate::lambda::{FunctionAttribute, LamLoc};
        use crate::lambda::lam_primitive::{Mutable, Primitive as P};
        let mut counts = [[0; 2]; 2];
        for (run, width) in [1_000usize, 10_000].into_iter().enumerate() {
            let mut a = LamArena::new();
            let mut locations = crate::lambda::LamLocTable::located(Default::default());
            let mut resolver = crate::js_ir::ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
            let values: Vec<_> = (0..width).map(|i| {
                locations.intern(crate::location::Location::new(Default::default(), i + 1, i + 8));
                resolver.set_module_path_override(&format!("M{i}"), format!("./M{i}.res.js"));
                let body = a.const_(Constant::Int { i: i as i32, comment: None });
                a.function_(0, &[], body, FunctionAttribute::default(), LamLoc::NONE)
            }).collect();
            let root = a.prim_raw(P::Pmakearray, &values, LamLoc::NONE);
            let export = Ident::new("answer", 2, crate::ident::IdentFlags::NONE);
            let root = a.prim_raw(P::Pmakeblock(TagInfo::ModuleExport(vec![export]), Mutable::Immutable), &[root], LamLoc::NONE);
            for (lent, (l, r)) in [(None, None), (Some(&locations), Some(&resolver))].into_iter().enumerate() {
                let warm = crate::bir::bridge::import_for_lowering(&a, root).0.unwrap();
                let input = crate::bir::bridge::import_for_lowering(&a, root).0.unwrap();
                drop(super::super::lower_with_resolver(warm, l, true, r, false, true, false).unwrap());
                let mut result = None;
                let allocations = allocation_counter::measure(|| {
                    result = Some(super::super::lower_with_resolver(input, l, true, r, false, true, false).unwrap());
                });
                let result = result.unwrap();
                assert_eq!(result.program.arena.vars.funcs.len(), width);
                println!("borrowed inputs width={width} lent={lent}: {allocations:?}");
                counts[run][lent] = allocations.count_total;
            }
        }
        assert_eq!(counts[0], counts[1], "allocation count must not scale with the table, resolver or headers");
        assert_eq!(counts[0][0], counts[0][1], "lending the table and resolver must not allocate");
    }

    #[inline(never)]
    fn allocation_window_start() { std::hint::black_box(()); }
    #[inline(never)]
    fn allocation_window_end() { std::hint::black_box(()); }

    #[test]
    fn export_consumption_does_not_empty_shared_block_metadata() {
        let mut source = LamArena::new();
        let name = Ident::new("answer", 700, crate::ident::IdentFlags::NONE);
        let tag = TagInfo::ModuleExport(vec![name]);
        let value = source.const_(Constant::Int { i: 42, comment: None });
        let root = source.prim_raw(crate::lambda::lam_primitive::Primitive::Pmakeblock(tag.clone(), crate::lambda::lam_primitive::Mutable::Immutable), &[value], crate::lambda::LamLoc::NONE);
        let input = crate::bir::bridge::import_for_lowering(&source, root).0.unwrap().into_imported(); let root = input.root;
        let mut state = State::new(input);
        let probed = state.probe(Cx::value(), root).unwrap();
        let shared = state.arena.block_info(&tag);
        let lowered = state.complete_unit(probed);
        assert_eq!(lowered.program.arena.block_tag(shared), &tag);
        assert_eq!(lowered.coerced.exports.len(), 1);
    }

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
        let input = crate::bir::bridge::import_for_lowering(&source, root).0.unwrap();
        let from_unit = lower(input, None, false, None, false, true, false).unwrap();
        let input = crate::bir::bridge::import_for_lowering(&source, root).0.unwrap().into_imported();
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
