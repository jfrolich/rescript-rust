//! The arity `Lam_pass_collect.collect_info` records for a bound function
//! (`lambda/lam_pass_collect.rs`, compiler/core/lam_pass_collect.ml and
//! lam_arity_analysis.ml), as an explicit pass.
//!
//! This fact is not maintained by the arena, and cannot be read from the
//! function node alone. `get_arity` of a function reads the recorded arity of
//! the variables its body ends in, and the table is filled in visiting order
//! and never cleared: a binding visited before the function it calls sees the
//! arity that function had after the previous `collect_info`, or none after
//! the first. The value therefore depends on how many collections ran and on
//! the trees they ran on (`the_recorded_arity_depends_on_the_collections_run`).
//! Maintaining it would need, per edit, the arities of every function whose
//! body ends in the edited binding, in the order of a traversal that has not
//! happened yet. So the legacy passes are reproduced as they are: one walk of
//! the unit per `collect_info`, in its order, over a dense table indexed by
//! variable that is carried from one walk to the next.
//!
//! Cost of one walk: the nodes of the unit, plus for each bound function and
//! each exported binding the tail of its value (`get_arity` follows bodies,
//! last sequence elements and every branch), as today. Size: one entry per
//! variable. The alias round does not read arities; the round that ports
//! `alpha_conversion` does.
use crate::bir::engine::Engine;
use crate::bir::*;
use crate::lambda::lam_arity::Arity;
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_compile_context::ExternalArityInfo;
use crate::lambda::lam_primitive::{Mutable, Primitive};

/// What the legacy table holds for a variable, as far as arities go.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) enum Recorded {
    /// No entry.
    #[default]
    Nothing,
    /// An entry that is not a function entry.
    Other,
    /// `FunctionId` with this arity.
    Function(Arity),
}

/// `Lam_compile_env.query_external_id_info` for arities.
pub(crate) type External<'a> = dyn FnMut(ImportId, &str) -> Option<ExternalArityInfo> + 'a;

/// The table, by variable.
#[derive(Default)]
pub(crate) struct Arities {
    recorded: Vec<Recorded>,
}

impl Arities {
    /// What is recorded for `var`.
    pub(crate) fn get(&self, var: VarId) -> &Recorded {
        self.recorded.get(var.index()).unwrap_or(&Recorded::Nothing)
    }
    fn set(&mut self, var: VarId, recorded: Recorded) {
        if self.recorded.len() <= var.index() {
            self.recorded.resize(var.index() + 1, Recorded::Nothing);
        }
        self.recorded[var.index()] = recorded;
    }

    /// `Lam_arity_analysis.get_arity` (lam_pass_collect.rs:81-230,
    /// lam_arity_analysis.ml:38-132), as a fold with an explicit stack.
    /// Every branch is evaluated; the legacy function stops at the first
    /// branch without information, which gives the same arity.
    fn arity(&self, b: &Bir, root: NodeId, external: &mut External<'_>) -> Arity {
        enum Task {
            Eval(NodeId),
            Merge(i32),
            Applied(i32),
            All(usize),
        }
        let mut tasks = vec![Task::Eval(root)];
        let mut values: Vec<Arity> = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                // lam_arity_analysis.ml:106.
                Task::Merge(n) => {
                    let body = values.pop().expect("body arity");
                    values.push(body.merge(n));
                }
                // lam_arity_analysis.ml:88-105.
                Task::Applied(mut arg_length) => {
                    let result = match values.pop().expect("callee arity") {
                        Arity::Na => Arity::na(),
                        Arity::Info {
                            mut arities,
                            variadic,
                        } => loop {
                            match arities.first().copied() {
                                Some(x) if arg_length == x => {
                                    arities.remove(0);
                                    break Arity::info(arities, variadic);
                                }
                                Some(x) if arg_length > x => {
                                    arities.remove(0);
                                    arg_length -= x;
                                }
                                Some(x) => {
                                    arities[0] = x - arg_length;
                                    break Arity::info(arities, variadic);
                                }
                                None => {
                                    break if variadic {
                                        Arity::raise()
                                    } else {
                                        Arity::na()
                                    };
                                }
                            }
                        },
                    };
                    values.push(result);
                }
                // `all_lambdas` (lam_arity_analysis.ml:134-149).
                Task::All(count) => {
                    let branches: Vec<Arity> = values.drain(values.len() - count..).collect();
                    let mut branches = branches.into_iter();
                    let mut acc = branches.next().unwrap_or_else(Arity::na);
                    for next in branches {
                        acc = match (acc, next) {
                            (
                                Arity::Info { arities, variadic },
                                Arity::Info {
                                    arities: other,
                                    variadic: other_variadic,
                                },
                            ) => Arity::merge_arities(&arities, &other, variadic, other_variadic),
                            _ => Arity::na(),
                        };
                        if acc == Arity::na() {
                            break;
                        }
                    }
                    values.push(acc);
                }
                Task::Eval(n) => match b.view(n) {
                    View::Var { var } => values.push(match self.get(var) {
                        Recorded::Function(arity) => arity.clone(),
                        Recorded::Nothing | Recorded::Other => Arity::na(),
                    }),
                    View::Const { .. } => values.push(Arity::non_function()),
                    View::Let { body, .. } | View::LetRec { body, .. } => {
                        tasks.push(Task::Eval(body))
                    }
                    View::Prim { args, primitive } => {
                        values.push(self.primitive(b, &b.primitive(primitive).primitive, args, external))
                    }
                    View::Global { .. } | View::Exit { .. } => values.push(Arity::na()),
                    View::Apply { callee, args, .. } => {
                        tasks.push(Task::Applied(args.len() as i32));
                        tasks.push(Task::Eval(callee));
                    }
                    View::Fun { body, .. } => {
                        tasks.push(Task::Merge(i32::from(b.node(n).aux())));
                        tasks.push(Task::Eval(body));
                    }
                    // lam_arity_analysis.ml:107-122: the default first.
                    View::Switch {
                        actions, header, ..
                    } => {
                        let cases = actions.len() - usize::from(b.switch(header).has_default);
                        tasks.push(Task::All(actions.len()));
                        tasks.extend(actions[..cases].iter().rev().copied().map(Task::Eval));
                        tasks.extend(actions[cases..].iter().copied().map(Task::Eval));
                    }
                    // lam_arity_analysis.ml:123-126: the default first.
                    View::StrSwitch {
                        actions, header, ..
                    } => {
                        let cases = actions.len() - usize::from(b.switch(header).has_default);
                        tasks.push(Task::All(actions.len()));
                        tasks.extend(actions[..cases].iter().rev().copied().map(Task::Eval));
                        tasks.extend(actions[cases..].iter().copied().map(Task::Eval));
                    }
                    View::Catch { handler, .. } => tasks.push(Task::Eval(handler)),
                    View::Try { body, handler, .. } => {
                        tasks.push(Task::All(2));
                        tasks.push(Task::Eval(handler));
                        tasks.push(Task::Eval(body));
                    }
                    View::TryFinally { body, .. } => tasks.push(Task::Eval(body)),
                    View::If { then_, else_, .. } => {
                        tasks.push(Task::All(2));
                        tasks.push(Task::Eval(else_));
                        tasks.push(Task::Eval(then_));
                    }
                    View::Seq { second, .. } => tasks.push(Task::Eval(second)),
                    // lam_arity_analysis.ml:132, and the default of the port.
                    _ => values.push(Arity::non_function()),
                },
            }
        }
        values.pop().expect("arity")
    }

    /// The primitive arm (lam_pass_collect.rs:96-141,
    /// lam_arity_analysis.ml:43-74).
    fn primitive(
        &self,
        b: &Bir,
        primitive: &Primitive,
        args: &[NodeId],
        external: &mut External<'_>,
    ) -> Arity {
        let module_field = |n: NodeId| match b.view(n) {
            View::Prim {
                args: [m],
                primitive,
            } => match (&b.primitive(primitive).primitive, b.view(*m)) {
                (Primitive::Pfield(_, FieldDbgInfo::Module { name }), View::Global { module }) => {
                    Some((module, *name))
                }
                _ => None,
            },
            _ => None,
        };
        match (primitive, args) {
            (Primitive::Pfield(_, FieldDbgInfo::Module { name }), [m])
                if b.node(*m).op() == Op::Global =>
            {
                let View::Global { module } = b.view(*m) else {
                    unreachable!()
                };
                match external(module, name.as_str()) {
                    Some(ExternalArityInfo::Single(arity)) => arity,
                    Some(ExternalArityInfo::Submodule(_)) | None => Arity::na(),
                }
            }
            (Primitive::Pfield(index, _), [inner]) if module_field(*inner).is_some() => {
                let (module, name) = module_field(*inner).expect("checked");
                match external(module, name.as_str()) {
                    Some(ExternalArityInfo::Submodule(arities)) => arities
                        .get(*index as usize)
                        .cloned()
                        .unwrap_or_else(Arity::na),
                    Some(ExternalArityInfo::Single(_)) | None => Arity::na(),
                }
            }
            (Primitive::Praise, _) => Arity::raise(),
            _ => Arity::na(),
        }
    }

    /// One `Lam_pass_collect.collect_info` (lam_pass_collect.rs:296-431,
    /// lam_pass_collect.ml:57-152) over the unit, in its visiting order.
    pub(crate) fn collect(&mut self, e: &Engine<'_>, root: NodeId, external: &mut External<'_>) {
        enum Task {
            Collect(NodeId),
            Bind(VarId, NodeId),
            /// lam_pass_collect.rs:383-389: after the value is collected.
            Exported(VarId, NodeId),
        }
        let b = e.bir();
        let mut tasks = vec![Task::Collect(root)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Exported(var, value) => {
                    if b.vars().flags(var).contains(VarFlags::EXPORTED) {
                        let arity = self.arity(b, value, external);
                        self.set(var, Recorded::Function(arity));
                    }
                }
                Task::Collect(n) => match b.view(n) {
                    View::Fun { body, header } => {
                        for param in b.function(header).params.iter() {
                            self.set(param, Recorded::Other);
                        }
                        tasks.push(Task::Collect(body));
                    }
                    View::Let { var, value, body } => {
                        tasks.push(Task::Collect(body));
                        if let Some(value) = value {
                            tasks.push(Task::Bind(var, value));
                        }
                    }
                    View::LetRec {
                        first,
                        values,
                        body,
                    } => {
                        tasks.push(Task::Collect(body));
                        for (index, value) in values.iter().enumerate().rev() {
                            tasks.push(Task::Bind(VarId(first.0 + index as u32), *value));
                        }
                    }
                    _ => tasks.extend(b.view(n).children().into_iter().rev().map(Task::Collect)),
                },
                // `collect_bind` (lam_pass_collect.rs:323-380).
                Task::Bind(var, value) => match b.view(value) {
                    View::Const { .. } | View::Global { .. } => self.set(var, Recorded::Other),
                    View::Prim { args, primitive } => {
                        match (&b.primitive(primitive).primitive, args) {
                            (Primitive::Pmakeblock(_, Mutable::Immutable), args) => {
                                self.set(var, Recorded::Other);
                                tasks.extend(args.iter().rev().copied().map(Task::Collect));
                            }
                            (Primitive::Psome | Primitive::PsomeNotNest, [x]) => {
                                self.set(var, Recorded::Other);
                                tasks.push(Task::Collect(*x));
                            }
                            (Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt, [x])
                                if b.node(*x).op() == Op::Var =>
                            {
                                self.set(var, Recorded::Other)
                            }
                            _ => {
                                tasks.push(Task::Exported(var, value));
                                tasks.push(Task::Collect(value));
                            }
                        }
                    }
                    // `alias_ident_or_global` (lam_pass_collect.rs:41-52).
                    View::Var { var: target } => {
                        let known = self.get(target).clone();
                        if known != Recorded::Nothing {
                            self.set(var, known);
                        }
                    }
                    View::Fun { body, header } => {
                        for param in b.function(header).params.iter() {
                            self.set(param, Recorded::Other);
                        }
                        let arity = self.arity(b, value, external);
                        self.set(var, Recorded::Function(arity));
                        tasks.push(Task::Collect(body));
                    }
                    _ => {
                        tasks.push(Task::Exported(var, value));
                        tasks.push(Task::Collect(value));
                    }
                },
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::bridge::import_lambda;
    use crate::bir::engine::testing::id;
    use crate::lambda::arena::LamArena;
    use crate::lambda::lam_constant::Constant as C;
    use crate::lambda::lam_stats::{IdKind, LamStats};
    use crate::lambda::{ApInfo, ApplyStatus, FunctionAttribute, LamLoc};

    /// `let rec f = x => g(x) and g = (y, z) => 1`: `f` is visited first.
    /// The first collection knows nothing about `g` and records that `f`
    /// takes one argument; the second finds `g` in the table and records
    /// that `f`, applied to one argument, returns a function of one more.
    /// The tree is the same both times.
    #[test]
    fn the_recorded_arity_depends_on_the_collections_run() {
        let mut a = LamArena::new();
        let (f, g, x, y, z) = (id("f", 1), id("g", 2), id("x", 3), id("y", 4), id("z", 5));
        let vg = a.var(g);
        let vx = a.var(x);
        let info = ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Uncurry,
        };
        let call = a.apply_raw(vg, &[vx], info);
        let attr = FunctionAttribute::default;
        let first = a.function_(1, &[x], call, attr(), LamLoc::NONE);
        let one = a.const_(C::int(1));
        let second = a.function_(2, &[y, z], one, attr(), LamLoc::NONE);
        let vf = a.var(f);
        let root = a.letrec(&[(f, first), (g, second)], vf);
        let mut imported = import_lambda(&a, root).unwrap();
        let root_node = imported.root;
        let e = Engine::new(&mut imported.arena);
        let mut meta = LamStats::new(vec![]);
        let mut ours = Arities::default();
        let mut seen = Vec::new();
        for _ in 0..2 {
            crate::lambda::lam_pass_collect::collect_info(&a, &mut meta, root);
            ours.collect(&e, root_node, &mut |_, _| None);
            let Some(IdKind::FunctionId { arity, .. }) = meta.ident_tbl.get(&f) else {
                panic!("function entry");
            };
            assert_eq!(ours.get(VarId(0)), &Recorded::Function(arity.clone()));
            seen.push(arity.clone());
        }
        assert_eq!(seen[0], Arity::info(vec![1], false));
        assert_eq!(seen[1], Arity::info(vec![1, 1], false));
    }
}
