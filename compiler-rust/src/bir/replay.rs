//! The `lambda-norm` shadow comparison (stage S4.1): do the Bir normalising
//! rules produce what `LamArena`'s smart constructors produce?
//!
//! Two comparisons per unit, both against the legacy constructors:
//!
//! 1. **Replay.** The input the legacy constructors saw exists only inside
//!    `raw_lambda::lower::Lowering`, as the lowered children at each call.
//!    `lower_traced` records every call (constructor, arguments, result).
//!    The replay builds the unit in a fresh `Bir`: a node lowering built
//!    plainly is imported as it is; where lowering called a smart
//!    constructor, the arguments are built into a plain node and given to
//!    the engine. The export must print like the lowered Lambda.
//! 2. **Renormalisation.** Lowering never calls `switch_with` or
//!    `string_switch_with`, and builds some nodes plainly on purpose. So the
//!    lowered unit is also rebuilt bottom-up through every legacy smart
//!    constructor, and compared with one normalising pass of the engine over
//!    the imported unit. This is what a pass that rebuilds a spine does to
//!    the nodes on it.
use super::bridge::{Imported, Importer, Unsupported, children, export_lambda, import_lambda};
use super::engine::{Engine, Stats};
use super::*;
use crate::fast_hash::AHashMap;
use crate::lambda::arena::{Lam, LamArena, Node as L};
use crate::raw_lambda::lower::Built;
use smallvec::SmallVec;

/// Rule firings of the two comparisons of one unit.
#[derive(Debug, Default, Clone)]
pub struct NormStats {
    /// Smart-constructor calls replayed.
    pub calls: u64,
    /// Rows fired while replaying lowering's calls.
    pub replayed: [u32; l::norm::ROWS],
    /// Rows fired by the normalising pass over the lowered unit.
    pub renormalised: [u32; l::norm::ROWS],
    /// Node pairs compared by row N11.
    pub compared: u64,
}

struct Replay<'a> {
    arena: &'a LamArena,
    importer: Importer,
    /// Results of replayed calls not yet used as a child.
    built: AHashMap<Lam, NodeId>,
    stats: Stats,
}

impl Replay<'_> {
    /// The Bir node of a lowered expression: the result of a replayed call,
    /// or a plain import of a node lowering built plainly.
    fn get(&mut self, root: Lam) -> Result<NodeId, Unsupported> {
        enum Work {
            Enter(Lam),
            Finish(L, usize),
        }
        let mut work = vec![Work::Enter(root)];
        let mut values: Vec<NodeId> = Vec::new();
        while let Some(task) = work.pop() {
            match task {
                Work::Enter(id) => {
                    if let Some(node) = self.built.remove(&id) {
                        values.push(node);
                        continue;
                    }
                    let node = self.arena.node(id);
                    let children = children(self.arena, node);
                    work.push(Work::Finish(node, children.len()));
                    work.extend(children.into_iter().rev().map(Work::Enter));
                }
                Work::Finish(node, count) => {
                    let start = values.len() - count;
                    let result = self.importer.node(self.arena, node, &values[start..])?;
                    values.truncate(start);
                    values.push(result);
                }
            }
        }
        Ok(values[0])
    }

    fn normalise(&mut self, node: NodeId) {
        let mut engine = Engine::new(&mut self.importer.bir);
        engine.normalise(node);
        for (total, fired) in self.stats.fired.iter_mut().zip(engine.stats.fired) {
            *total += fired;
        }
        self.stats.compared += engine.stats.compared;
    }

    fn call(&mut self, call: &Built) -> Result<(), Unsupported> {
        let (result, node) = match call {
            Built::If {
                cond,
                then_,
                else_,
                result,
            } => {
                let c = [self.get(*cond)?, self.get(*then_)?, self.get(*else_)?];
                let view = View::If {
                    condition: c[0],
                    then_: c[1],
                    else_: c[2],
                };
                (*result, self.importer.bir.new_node(view, 0))
            }
            Built::Seq {
                first,
                second,
                result,
            } => {
                let (first, second) = (self.get(*first)?, self.get(*second)?);
                let view = View::Seq { first, second };
                (*result, self.importer.bir.new_node(view, 0))
            }
            Built::Prim {
                primitive,
                loc,
                args,
                result,
            } => {
                let args: SmallVec<[NodeId; 4]> = args
                    .iter()
                    .map(|arg| self.get(*arg))
                    .collect::<Result<_, _>>()?;
                let primitive = self.importer.bir.intern_prim(PrimPayload {
                    primitive: primitive.clone(),
                    loc: *loc,
                });
                let view = View::Prim {
                    args: &args,
                    primitive,
                };
                (*result, self.importer.bir.new_node(view, 0))
            }
            Built::Apply {
                func,
                args,
                info,
                result,
            } => {
                let callee = self.get(*func)?;
                let args: SmallVec<[NodeId; 4]> = args
                    .iter()
                    .map(|arg| self.get(*arg))
                    .collect::<Result<_, _>>()?;
                let info = self.importer.bir.apply_info(info.clone());
                let view = View::Apply {
                    callee,
                    args: &args,
                    info,
                };
                (*result, self.importer.bir.new_node(view, 0))
            }
        };
        self.normalise(node);
        if let Some(unused) = self.built.insert(result, node) {
            // Two calls returned one node: only a shared (non-tree) lowering
            // can, and the bridge does not represent sharing.
            self.importer.bir.release(unused);
            return Err(Unsupported("shared Lambda node"));
        }
        Ok(())
    }
}

/// Build the unit by replaying lowering's smart-constructor calls through
/// the normalising rules. `raw` is the raw root the calls were made for;
/// `lowered` is what lowering returned.
pub fn replay_lowering(
    arena: &LamArena,
    raw: Lam,
    lowered: Lam,
    trace: &[Built],
) -> Result<(Imported, Stats), Unsupported> {
    let mut replay = Replay {
        arena,
        importer: Importer::default(),
        built: AHashMap::default(),
        stats: Stats::default(),
    };
    replay.importer.bir.begin_bulk();
    // Binders and static catch headers come from the raw tree, top-down:
    // raw and lowered Lambda share them, and a call's argument may hold an
    // exit or a binder that the constructor then drops. Raw Lambda shares
    // some nodes; lowering copies them, so each is registered once here.
    let mut seen = vec![false; arena.node_count()];
    let mut stack = vec![raw];
    while let Some(id) = stack.pop() {
        if std::mem::replace(&mut seen[id.index()], true) {
            continue;
        }
        let node = arena.node(id);
        replay.importer.binders(arena, node)?;
        stack.extend(children(arena, node).into_iter().rev());
    }
    for call in trace {
        replay.call(call)?;
    }
    let root = replay.get(lowered)?;
    // Results lowering itself dropped (an ignored argument).
    let mut unused: Vec<(Lam, NodeId)> = replay.built.drain().collect();
    unused.sort_unstable_by_key(|(lam, _)| lam.index());
    for (_, node) in unused {
        replay.importer.bir.release(node);
    }
    replay.importer.bir.try_finish_bulk(root)?;
    Ok((replay.importer.finish(root), replay.stats))
}

/// Rebuild `root` bottom-up through every `LamArena` smart constructor: what
/// a pass's rebuild does to each node of a changed spine.
pub fn legacy_renormalise(a: &mut LamArena, root: Lam) -> Lam {
    enum Work {
        Enter(Lam),
        Finish(Lam, usize),
    }
    let mut work = vec![Work::Enter(root)];
    let mut values: Vec<Lam> = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            Work::Enter(id) => {
                let kids = children(a, a.node(id));
                work.push(Work::Finish(id, kids.len()));
                work.extend(kids.into_iter().rev().map(Work::Enter));
            }
            Work::Finish(id, count) => {
                let start = values.len() - count;
                let c: SmallVec<[Lam; 8]> = SmallVec::from_slice(&values[start..]);
                values.truncate(start);
                let rebuilt = match a.node(id) {
                    L::Var(_) | L::GlobalModule(_) | L::Const(_) | L::Break | L::Continue => id,
                    L::Apply { info, .. } => {
                        let args = a.add_list(&c[1..]);
                        a.apply_with(c[0], args, info)
                    }
                    L::Function { info, .. } => a.function_with(info, c[0]),
                    L::Let { kind, id, .. } => a.let_with(kind, id, c[0], c[1]),
                    L::LetRec { ids, .. } => {
                        let values = a.add_list(&c[..c.len() - 1]);
                        a.letrec_with(ids, values, c[c.len() - 1])
                    }
                    L::Prim { info, .. } => a.prim_with_id(info, &c),
                    L::Switch { info, .. } => {
                        let actions = a.add_list(&c[1..]);
                        a.switch_with(c[0], actions, info)
                    }
                    L::StringSwitch { info, .. } => {
                        let actions = a.add_list(&c[1..]);
                        a.string_switch_with(c[0], actions, info)
                    }
                    L::StaticRaise { label, .. } => a.static_raise(label, &c),
                    L::StaticCatch { info, .. } => a.static_catch_with(c[0], info, c[1]),
                    L::TryWith { id, .. } => a.try_with(c[0], id, c[1]),
                    L::TryFinally { .. } => a.try_finally(c[0], c[1]),
                    L::If { .. } => a.if_(c[0], c[1], c[2]),
                    L::Sequence(..) => a.seq(c[0], c[1]),
                    L::While(..) => a.while_(c[0], c[1]),
                    L::For { dir, id, .. } => a.for_with(id, c[0], c[1], dir, c[2]),
                    L::ForOf { id, .. } => a.push(L::ForOf {
                        id,
                        iter: c[0],
                        body: c[1],
                    }),
                    L::ForAwaitOf { id, .. } => a.push(L::ForAwaitOf {
                        id,
                        iter: c[0],
                        body: c[1],
                    }),
                    L::Assign { id, .. } => a.assign_with(id, c[0]),
                };
                values.push(rebuilt);
            }
        }
    }
    values[0]
}

fn dump(arena: &LamArena, root: Lam) -> anyhow::Result<Vec<u8>> {
    let mut out = Vec::new();
    crate::lambda::sexp_lambda::print_lambda(&arena.export(root), &mut out)?;
    Ok(out)
}

fn first_difference(before: &[u8], after: &[u8]) -> usize {
    let before = String::from_utf8_lossy(before);
    let after = String::from_utf8_lossy(after);
    before
        .lines()
        .zip(after.lines())
        .position(|(a, b)| a != b)
        .unwrap_or_else(|| before.lines().count().min(after.lines().count()))
        + 1
}

fn exported(
    imported: &Imported,
    unit: &str,
    what: &str,
) -> anyhow::Result<Result<Vec<u8>, Unsupported>> {
    imported
        .arena
        .validate(Some(imported.root), false)
        .map_err(|message| anyhow::anyhow!("{unit}: lambda-norm {what} validation: {message}"))?;
    Ok(match export_lambda(imported) {
        Ok(program) => Ok(dump(&program.arena, program.root)?),
        Err(reason) => Err(reason),
    })
}

/// Both comparisons for one unit. `arena` holds the unit's raw Lambda at
/// `raw` (lowering leaves raw nodes in the arena it returns). An
/// unsupported shape is `Ok(Err(reason))`; a difference is an error.
pub fn compare(
    arena: &LamArena,
    raw: Lam,
    unit: &str,
) -> anyhow::Result<Result<NormStats, Unsupported>> {
    let mut stats = NormStats::default();
    let (mut legacy, lowered, trace) = crate::raw_lambda::lower::lower_traced(arena, raw);
    stats.calls = trace.len() as u64;
    let expected = dump(&legacy, lowered)?;

    let (replayed, fired) = match replay_lowering(&legacy, raw, lowered, &trace) {
        Ok(result) => result,
        Err(reason) => return Ok(Err(reason)),
    };
    stats.replayed = fired.fired;
    stats.compared = fired.compared;
    let actual = match exported(&replayed, unit, "replay")? {
        Ok(actual) => actual,
        Err(reason) => return Ok(Err(reason)),
    };
    if expected != actual {
        let line = first_difference(&expected, &actual);
        anyhow::bail!("{unit}: lambda-norm replay mismatch at line {line}");
    }

    let mut imported = match import_lambda(&legacy, lowered) {
        Ok(imported) => imported,
        Err(reason) => return Ok(Err(reason)),
    };
    {
        let mut engine = Engine::new(&mut imported.arena);
        engine.normalise_tree(imported.root);
        stats.renormalised = engine.stats.fired;
        stats.compared += engine.stats.compared;
    }
    let actual = match exported(&imported, unit, "renormalisation")? {
        Ok(actual) => actual,
        Err(reason) => return Ok(Err(reason)),
    };
    let rebuilt = legacy_renormalise(&mut legacy, lowered);
    let expected = dump(&legacy, rebuilt)?;
    if expected != actual {
        let line = first_difference(&expected, &actual);
        anyhow::bail!("{unit}: lambda-norm renormalisation mismatch at line {line}");
    }
    Ok(Ok(stats))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::lam_constant::Constant as C;
    use crate::lambda::lam_primitive::Primitive;
    use crate::lambda::{ApInfo, ApplyStatus, FunctionAttribute, LamLoc};

    /// Raw Lambda whose lowering calls every traced constructor:
    /// `if c then (((x, y) => x + y)(1, 2); ()) else assert false`.
    fn raw_unit(a: &mut LamArena) -> Lam {
        let id = |name: &str, stamp| {
            crate::ident::Ident::new(name, stamp, crate::ident::IdentFlags::NONE)
        };
        let (x, y) = (id("x", 1), id("y", 2));
        let (vx, vy) = (a.var(x), a.var(y));
        let sum = a.prim_raw(Primitive::Paddint, &[vx, vy], LamLoc::NONE);
        let f = a.function_(2, &[x, y], sum, FunctionAttribute::default(), LamLoc::NONE);
        let args = [a.const_(C::int(1)), a.const_(C::int(2))];
        let info = ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Uncurry,
        };
        let call = a.apply_raw(f, &args, info);
        let unit = a.unit();
        let then_ = a.seq_raw(call, unit);
        let else_ = a.const_(C::Int {
            i: 0,
            comment: Some(Box::new(
                crate::lambda::lam_constant::PointerInfo::AssertFalse,
            )),
        });
        let c = a.var(id("c", 3));
        let zero = a.const_(C::int(0));
        let cond = a.prim_raw(
            Primitive::Pintcomp(crate::lambda::lam_compat::Comparison::Neq),
            &[c, zero],
            LamLoc::NONE,
        );
        a.if_raw(cond, then_, else_)
    }

    #[test]
    fn a_unit_replays_and_renormalises_like_the_legacy_constructors() {
        let mut a = LamArena::new();
        let raw = raw_unit(&mut a);
        let stats = compare(&a, raw, "Unit.res").unwrap().unwrap();
        // The condition, the sum, the application, the sequence, the `if`.
        assert_eq!(stats.calls, 5);
        let fired = |row: &str| {
            let i = l::norm::ROW_NAMES
                .iter()
                .position(|name| *name == row)
                .unwrap();
            stats.replayed[i]
        };
        // The application is an eta redex whose result folds; the `if` has
        // an `assert false` branch.
        assert_eq!((fired("N13"), fired("N2"), fired("N5")), (1, 1, 1));
        assert_eq!(stats.renormalised, [0; l::norm::ROWS]);
    }

    #[test]
    fn a_replay_that_disagrees_with_lowering_prints_differently() {
        let mut a = LamArena::new();
        let raw = raw_unit(&mut a);
        let (legacy, lowered, mut trace) = crate::raw_lambda::lower::lower_traced(&a, raw);
        let expected = dump(&legacy, lowered).unwrap();
        // Give the rule another input than the constructor saw: the
        // comparison `c != 0` with its operands swapped.
        let call = trace
            .iter_mut()
            .find_map(|call| match call {
                Built::Prim { args, .. } if args.len() == 2 => Some(args),
                _ => None,
            })
            .unwrap();
        call.swap(0, 1);
        let (replayed, _) = replay_lowering(&legacy, raw, lowered, &trace).unwrap();
        let actual = exported(&replayed, "Unit.res", "replay").unwrap().unwrap();
        assert_ne!(expected, actual);
        assert!(first_difference(&expected, &actual) >= 1);
    }
}
