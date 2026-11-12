//! K1–K6: C:1529 compile_expr and its Let/Sequence/Function context arms.
use super::*;
use crate::bir::{FuncId, VarSpan};

/// Decoded structural operands saved across child visits; no source re-read.
pub(super) enum Resume {
    Let {
        var: VarId,
        kind: LetKind,
        value: Option<NodeId>,
        body: NodeId,
    },
    Seq {
        first: NodeId,
        second: NodeId,
    },
    Fun {
        body: NodeId,
        header: FuncId,
    },
}
impl State {
    /// K4/K2/K10: C:2411 compile_let_binding_output, C:4603 compile_effect_output,
    /// C:1997 with_function_scope. Preserve order and reset function boundaries.
    pub(super) fn expression_children(
        &self,
        cx: Cx,
        resume: &Resume,
        into: &mut Vec<(Cx, NodeId)>,
    ) {
        match *resume {
            Resume::Let {
                var,
                kind,
                value,
                body,
            } => {
                if let Some(value) = value {
                    into.push((
                        Cx {
                            cont: Cont::Declare(kind, var),
                            ..cx
                        },
                        value,
                    ));
                }
                into.push((cx, body));
            }
            Resume::Seq { first, second } => {
                into.push((
                    Cx {
                        cont: Cont::Effect(Tail::No),
                        ..cx
                    },
                    first,
                ));
                into.push((cx, second));
            }
            Resume::Fun { body, header } => {
                let mut function = Cx::returning();
                function.return_unit = self.arena.function_attributes(header).return_unit;
                into.push((function, body));
            }
        }
    }
    /// K4/K2/K10: C:2411 compile_let_binding_output / C:4603 compile_effect_output /
    /// C:1997 with_function_scope. Consume each non-speculative child before the
    /// next sibling; a declaration cannot be delayed past the body's statements.
    pub(super) fn expression_child(
        &mut self,
        cx: Cx,
        resume: &Resume,
        index: usize,
        child: Probed,
    ) -> Probed {
        let force = match resume {
            Resume::Let { value, .. } => value.is_some() && index == 0,
            Resume::Seq { .. } => index == 0,
            Resume::Fun { .. } => true,
        };
        if force {
            Probed::Out(self.realize(cx, child))
        } else {
            child
        }
    }
    /// K0/K2/K10: C:119 append, C:4715 append_effect_output, C:562 function_expr.
    pub(super) fn finish_expression(
        &mut self,
        cx: Cx,
        resume: Resume,
        mut children: impl Iterator<Item = Probed>,
    ) -> Probed {
        match resume {
            Resume::Let { value, .. } => {
                let first = value.map(|_| match children.next().expect("binding output") {
                    Probed::Out(out) => out,
                    Probed::Free(_) => unreachable!("binding was realized before body"),
                });
                let body = self.realize(cx, children.next().expect("let body"));
                let value = body.value;
                Probed::Out(match first {
                    Some(first) => self.statements.append(first, body, value),
                    None => body,
                })
            }
            Resume::Seq { .. } => {
                let Probed::Out(mut first) = children.next().expect("sequence head") else {
                    unreachable!("head was realized")
                };
                let second = children.next().expect("sequence tail");
                if first.stmts.len == 0 && first.finished == Finished::False {
                    if let Probed::Free(second) = second {
                        return Probed::Free(match first.value {
                            Some(first) => self.free.push(Free::Seq { first, second }),
                            None => second,
                        });
                    }
                }
                if let Some(value) = first.value.take() {
                    self.drop_pure_effect(value);
                }
                let second = self.realize(cx, second);
                let value = second.value;
                Probed::Out(self.statements.append(first, second, value))
            }
            Resume::Fun { header, .. } => {
                let Probed::Out(body) = children.next().expect("function body") else {
                    unreachable!("return was realized")
                };
                assert!(body.value.is_none());
                let list = self.statements.take_list(&mut self.arena, body.stmts);
                let body = self.arena.block_from_list(list);
                let source_loc = self
                    .located_functions
                    .get(header.index())
                    .copied()
                    .unwrap_or(false)
                    .then_some(self.arena.function(header).loc);
                let attr = self.arena.function_attributes(header);
                let header = if attr.one_unit_arg {
                    let attr = attr.clone();
                    let loc = self.arena.function(header).loc;
                    self.arena.function_header(VarSpan::default(), attr, loc)
                } else {
                    header
                };
                let value = self.pure_expression(View::JFun { body, header }, 0);
                if let Some(loc) = source_loc {
                    self.arena
                        .set_cold(value, crate::bir::Cold { loc, comment: None });
                    let mut flags = self.arena.node(value).flags();
                    flags.0 |= crate::bir::NodeFlags::JS_LOC_PRESENT;
                    self.arena.nodes[value.index()].set_flags(flags);
                }
                self.probe_leaf(cx, value)
            }
        }
    }
    /// K2: O:339 push_effect_expression. This slice's expression producers are
    /// strictly pure; unsupported producers never reach this operation.
    pub(super) fn drop_pure_effect(&mut self, value: NodeId) {
        crate::bir::j::norm::discard_pure_effect(&mut self.arena, value);
    }
}
