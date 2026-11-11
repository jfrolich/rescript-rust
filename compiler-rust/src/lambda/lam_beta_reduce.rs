//! `Lam_beta_reduce` and `Lam_bounded_vars` over the Lambda arena.

use ahash::AHashMap as HashMap;
use ahash::AHashSet;

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::LamLoc;
use crate::lambda::arena::{Lam, LamArena, Node};
use crate::lambda::lam_analysis::{delay_safe, no_side_effects};
use crate::lambda::lam_closure::StatsMap;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_hit::hit_variable;
use crate::lambda::lam_pass_collect::kind_of_lambda_block;
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::lam_stats::{IdKind, IdentTable};
use crate::lambda::lam_subst::Subst;
use crate::lambda::lam_util::refine_let;

/// How the evaluation of an argument may move with respect to other code
/// (lam_beta_reduce_util.ml:42-46).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Motion {
    /// No side effects, and depends on no state that may change.
    Anywhere,
    /// No side effects, but reads state that may change.
    Reads,
    Effects,
}

fn motion(a: &LamArena, assignable: &AHashSet<Ident>, lam: Lam) -> Motion {
    if delay_safe(a, assignable, lam) {
        Motion::Anywhere
    } else if no_side_effects(a, lam) {
        Motion::Reads
    } else {
        Motion::Effects
    }
}

/// Whether code of motions `a` and `b` can give other results when it runs
/// in the other order.
fn conflict(a: Motion, b: Motion) -> bool {
    matches!(
        (a, b),
        (Motion::Effects, Motion::Reads | Motion::Effects) | (Motion::Reads, Motion::Effects)
    )
}

/// The substitutions of one `simple_beta_reduce` and the code the reduced
/// body evaluates, in order, each with its rank in the call: a parameter's
/// position, or `params.len()` for a variable the body reads itself.
struct SimpleReduction<'p> {
    indices: HashMap<Ident, usize>,
    args: &'p [Lam],
    motions: smallvec::SmallVec<[Motion; 8]>,
    used: smallvec::SmallVec<[bool; 8]>,
    evaluated: smallvec::SmallVec<[(usize, Motion); 8]>,
    body_rank: usize,
}

impl SimpleReduction<'_> {
    /// Records that the reduced body evaluates code of `motion`; `None` for
    /// code with side effects in an operand that may not be evaluated.
    fn evaluate(&mut self, conditional: bool, rank: usize, motion: Motion) -> Option<()> {
        if conditional && motion == Motion::Effects {
            return None;
        }
        self.evaluated.push((rank, motion));
        Some(())
    }

    /// The operand for the variable `lam`: its parameter's argument, used at
    /// most once, or `lam` itself.
    fn variable(
        &mut self,
        a: &LamArena,
        assignable: &AHashSet<Ident>,
        conditional: bool,
        lam: Lam,
        x: Ident,
    ) -> Option<Lam> {
        match self
            .indices
            .get(&x)
            .copied()
            .filter(|i| *i < self.used.len())
        {
            Some(i) if self.used[i] => None,
            Some(i) => {
                self.used[i] = true;
                self.evaluate(conditional, i, self.motions[i])?;
                Some(self.args[i])
            }
            None => {
                self.evaluate(conditional, self.body_rank, motion(a, assignable, lam))?;
                Some(lam)
            }
        }
    }

    /// Substitutes in the operands from left to right; those from position
    /// `conditional_from` on may not be evaluated.
    fn operands(
        &mut self,
        a: &LamArena,
        assignable: &AHashSet<Ident>,
        conditional_from: usize,
        lams: &[Lam],
    ) -> Option<smallvec::SmallVec<[Lam; 8]>> {
        let mut result = smallvec::SmallVec::with_capacity(lams.len());
        for (i, &lam) in lams.iter().enumerate() {
            match a.node(lam) {
                Node::Var(x) => result.push(self.variable(
                    a,
                    assignable,
                    i >= conditional_from,
                    lam,
                    a.ident(x),
                )?),
                Node::Const(_) => result.push(lam),
                _ => return None,
            }
        }
        Some(result)
    }

    /// The reduced term runs the unused arguments first, then what the body
    /// evaluates. Code that conflicts keeps its order in the call.
    fn in_call_order(&self) -> bool {
        let order: smallvec::SmallVec<[(usize, Motion); 16]> = (0..self.used.len())
            .filter(|i| !self.used[*i])
            .map(|i| (i, self.motions[i]))
            .chain(self.evaluated.iter().copied())
            .collect();
        order.iter().enumerate().all(|(k, &(rank, m))| {
            order[k + 1..]
                .iter()
                .all(|&(later_rank, later)| rank <= later_rank || !conflict(m, later))
        })
    }
}

/// `Lam_beta_reduce_util.simple_beta_reduce` (lam_beta_reduce_util.ml:25-193):
/// a body that is one primitive or one call of a variable or module field,
/// whose operands are variables and constants each parameter fills at most
/// once. Each argument goes where the body uses its parameter, and an unused
/// one is sequenced before the body, so the arguments run in the body's order
/// rather than the call's: the reduction is kept only when that changes
/// nothing. Two arguments that both have side effects, or where one has side
/// effects and the other reads state they can change, keep their order (the
/// variables the body reads count as arguments after the last), and an
/// argument with side effects never goes to the right operand of `&&` or
/// `||`.
pub fn simple_beta_reduce(
    a: &mut LamArena,
    assignable: &AHashSet<Ident>,
    params: &[Ident],
    body: Lam,
    args: &[Lam],
) -> Option<Lam> {
    let n = params.len().min(args.len());
    let start = |a: &LamArena| SimpleReduction {
        indices: params
            .iter()
            .enumerate()
            .map(|(index, param)| (*param, index))
            .collect(),
        args,
        motions: args[..n]
            .iter()
            .map(|arg| motion(a, assignable, *arg))
            .collect(),
        used: smallvec::SmallVec::from_elem(false, n),
        evaluated: smallvec::SmallVec::new(),
        body_rank: params.len(),
    };
    // `Lam_beta_reduce_util.seq_unused`: sequence the unused arguments
    // before the body, in parameter order.
    let wrap_unused = |a: &mut LamArena, used: &[bool], mut result: Lam| {
        for index in (0..n).rev() {
            if !used[index] {
                result = a.seq(args[index], result);
            }
        }
        result
    };

    match a.node(body) {
        Node::Prim { args: pargs, info } => {
            let mut r = start(a);
            let conditional_from = if a.prim_payload(info).primitive.may_skip_operands() {
                1
            } else {
                usize::MAX
            };
            let new_args = r.operands(a, assignable, conditional_from, a.list(pargs))?;
            if !r.in_call_order() {
                return None;
            }
            let new_args = a.add_list(&new_args);
            let result = a.prim_with(info, new_args);
            Some(wrap_unused(a, &r.used, result))
        }
        Node::Apply {
            func,
            args: fargs,
            info,
        } => {
            let simple_func = match a.node(func) {
                Node::Var(_) => true,
                Node::Prim { .. } => matches!(
                    a.as_prim(func),
                    Some((Primitive::Pfield(_, _), [m], _)) if matches!(a.node(*m), Node::GlobalModule(_))
                ),
                _ => false,
            };
            if !simple_func {
                return None;
            }
            let mut r = start(a);
            // The function is evaluated before the arguments.
            let new_func = match a.node(func) {
                Node::Var(f) => r.variable(a, assignable, false, func, a.ident(f))?,
                _ => func,
            };
            let new_args = r.operands(a, assignable, usize::MAX, a.list(fargs))?;
            if !r.in_call_order() {
                return None;
            }
            let new_args = a.add_list(&new_args);
            let result = a.apply_raw_with(new_func, new_args, info);
            Some(wrap_unused(a, &r.used, result))
        }
        _ => None,
    }
}

/// `Lam_beta_reduce.no_names_beta_reduce` (lam_beta_reduce.ml:206-215): the
/// first parameter's binding is outermost, so the arguments evaluate in call
/// order.
pub fn no_names_beta_reduce(
    a: &mut LamArena,
    assignable: &AHashSet<Ident>,
    params: &[Ident],
    body: Lam,
    args: &[Lam],
) -> Lam {
    if let Some(result) = simple_beta_reduce(a, assignable, params, body, args) {
        return result;
    }
    let mut result = body;
    for (param, arg) in params.iter().zip(args).rev() {
        result = refine_let(a, LetKind::Strict, *param, *arg, result);
    }
    result
}

/// `Lam_beta_reduce.read_before_effects` (lam_beta_reduce.ml:52-92): whether
/// `body` reads `param` only before it runs code with side effects. A read in
/// code that may run later, such as a function or a loop, does not count as
/// before.
fn read_before_effects(a: &LamArena, param: &Ident, body: Lam) -> bool {
    /// `Err(())`: a read after code with side effects.
    fn walk(a: &LamArena, param: &Ident, effects: &mut bool, lam: Lam) -> Result<(), ()> {
        match a.node(lam) {
            Node::Var(v) => {
                if *effects && a.ident(v).same(param) {
                    return Err(());
                }
            }
            Node::Const(_) | Node::GlobalModule(_) => {}
            Node::Prim { args, .. } => {
                for &arg in a.list(args) {
                    walk(a, param, effects, arg)?;
                }
                if !no_side_effects(a, lam) {
                    *effects = true;
                }
            }
            Node::Apply { func, args, .. } => {
                walk(a, param, effects, func)?;
                for &arg in a.list(args) {
                    walk(a, param, effects, arg)?;
                }
                *effects = true;
            }
            Node::Let { value, body, .. } => {
                walk(a, param, effects, value)?;
                walk(a, param, effects, body)?;
            }
            Node::Sequence(first, second) => {
                walk(a, param, effects, first)?;
                walk(a, param, effects, second)?;
            }
            Node::If { cond, then_, else_ } => {
                walk(a, param, effects, cond)?;
                let before = *effects;
                walk(a, param, effects, then_)?;
                let after_then = *effects;
                *effects = before;
                walk(a, param, effects, else_)?;
                *effects = *effects || after_then;
            }
            Node::Function { .. }
            | Node::LetRec { .. }
            | Node::Switch { .. }
            | Node::StringSwitch { .. }
            | Node::StaticRaise { .. }
            | Node::StaticCatch { .. }
            | Node::TryWith { .. }
            | Node::TryFinally { .. }
            | Node::While(..)
            | Node::For { .. }
            | Node::ForOf { .. }
            | Node::ForAwaitOf { .. }
            | Node::Assign { .. }
            | Node::Break
            | Node::Continue => {
                if hit_variable(a, param, lam) {
                    return Err(());
                }
                if !no_side_effects(a, lam) {
                    *effects = true;
                }
            }
        }
        Ok(())
    }
    walk(a, param, &mut false, body).is_ok()
}

/// `Lam_beta_reduce.can_move` (lam_beta_reduce.ml:94-105). The arguments of
/// a call run left to right, then the body. Putting the argument for `param`
/// where `body` reads it instead moves it after the arguments to its right
/// and the code of `body` before the read. That changes nothing when it reads
/// no state that may change. One that only reads may still move when no
/// argument to its right has side effects (`effects_after`) and `body` reads
/// it before any.
fn can_move(
    a: &LamArena,
    assignable: &AHashSet<Ident>,
    effects_after: bool,
    param: &Ident,
    body: Lam,
    arg: Lam,
) -> bool {
    delay_safe(a, assignable, arg)
        || (no_side_effects(a, arg) && !effects_after && read_before_effects(a, param, body))
}

/// `Lam_beta_reduce.effects_after` (lam_beta_reduce.ml:107-113): for each
/// argument, whether an argument to its right has side effects.
fn effects_after(a: &LamArena, args: &[Lam]) -> smallvec::SmallVec<[bool; 8]> {
    let mut result = smallvec::SmallVec::from_elem(false, args.len());
    let mut effects = false;
    for (i, &arg) in args.iter().enumerate().rev() {
        result[i] = effects;
        effects = effects || !no_side_effects(a, arg);
    }
    result
}

/// `Lam_beta_reduce.propagate_beta_reduce` (lam_beta_reduce.ml:47-74).
pub fn propagate_beta_reduce(
    a: &mut LamArena,
    ident_tbl: &mut IdentTable,
    id_gen: &IdGenerator,
    assignable: &AHashSet<Ident>,
    params: &[Ident],
    body: Lam,
    args: &[Lam],
) -> Lam {
    propagate(a, ident_tbl, id_gen, assignable, None, params, body, args)
}

/// `Lam_beta_reduce.propagate_beta_reduce_with_map` (lam_beta_reduce.ml:76-115).
#[allow(clippy::too_many_arguments)]
pub fn propagate_beta_reduce_with_map(
    a: &mut LamArena,
    ident_tbl: &mut IdentTable,
    id_gen: &IdGenerator,
    assignable: &AHashSet<Ident>,
    stats: &StatsMap,
    params: &[Ident],
    body: Lam,
    args: &[Lam],
) -> Lam {
    propagate(
        a,
        ident_tbl,
        id_gen,
        assignable,
        Some(stats),
        params,
        body,
        args,
    )
}

/// An argument goes where the body reads its parameter only when
/// `can_move` allows it, so the arguments otherwise evaluate in call order
/// (lam_beta_reduce.ml:115-201).
#[allow(clippy::too_many_arguments)]
fn propagate(
    a: &mut LamArena,
    ident_tbl: &mut IdentTable,
    id_gen: &IdGenerator,
    assignable: &AHashSet<Ident>,
    stats: Option<&StatsMap>,
    params: &[Ident],
    body: Lam,
    args: &[Lam],
) -> Lam {
    if let Some(result) = simple_beta_reduce(a, assignable, params, body, args) {
        return result;
    }
    let mut rest_bindings: smallvec::SmallVec<[(Ident, Lam); 8]> = smallvec::SmallVec::new();
    let mut substitution: Subst = HashMap::new();
    let effects_after = effects_after(a, args);
    for ((param, &arg), &effects_after) in params.iter().zip(args).zip(&effects_after) {
        match a.node(arg) {
            Node::Const(_) => {
                substitution.insert(*param, arg);
            }
            Node::Var(_) if can_move(a, assignable, effects_after, param, body, arg) => {
                substitution.insert(*param, arg);
            }
            Node::GlobalModule(_) if stats.is_some() => {
                let new_param = param.rename(id_gen);
                rest_bindings.push((new_param, arg));
                let v = a.var(new_param);
                substitution.insert(*param, v);
            }
            _ => {
                if let Some(stats) = stats
                    && !matches!(a.node(arg), Node::Var(_))
                    && no_side_effects(a, arg)
                    && stats
                        .get(param)
                        .is_some_and(|stat| stat.top_and_used_zero_or_one())
                    && can_move(a, assignable, effects_after, param, body, arg)
                {
                    substitution.insert(*param, arg);
                    continue;
                }
                let new_param = param.rename(id_gen);
                let boxed = is_boxed_optional_binding(a, arg);
                let binding = if boxed {
                    a.prim(Primitive::Pidentity, &[arg], LamLoc::NONE)
                } else {
                    arg
                };
                rest_bindings.push((new_param, binding));
                let v = a.var(new_param);
                let replacement = if boxed {
                    a.prim(Primitive::Pidentity, &[v], LamLoc::NONE)
                } else {
                    v
                };
                substitution.insert(*param, replacement);
            }
        }
    }
    let mut result = rewrite_bounded_vars(a, &mut substitution, body, id_gen);
    // OCaml builds `rest_bindings` in reverse parameter order and folds it
    // left, making the first source argument's binding outermost.
    for (param, arg) in rest_bindings.into_iter().rev() {
        register_bound_param_kind(a, ident_tbl, &param, arg);
        result = refine_let(a, LetKind::Strict, param, arg, result);
    }
    result
}

/// The `meta.ident_tbl` update of `propagate_beta_reduce`
/// (lam_beta_reduce.ml:66-73, 107-114).
fn register_bound_param_kind(a: &LamArena, ident_tbl: &mut IdentTable, param: &Ident, arg: Lam) {
    match a.as_prim(arg) {
        Some((Primitive::Pmakeblock(_, Mutable::Immutable), args, _)) => {
            ident_tbl.insert(*param, kind_of_lambda_block(a, args));
        }
        Some((Primitive::Psome | Primitive::PsomeNotNest, [x], _)) => {
            ident_tbl.insert(*param, IdKind::NormalOptional(*x));
        }
        _ => {}
    }
}

fn is_boxed_optional_binding(a: &LamArena, arg: Lam) -> bool {
    matches!(
        a.as_prim(arg),
        Some((Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt, _, _))
    )
}

/// `Lam_bounded_vars.rewrite`: substitute and give every binder of `lam` a
/// fresh name, rebuilding through the smart constructors.
fn rewrite_bounded_vars(a: &mut LamArena, s: &mut Subst, lam: Lam, id_gen: &IdGenerator) -> Lam {
    fn rebind(a: &mut LamArena, id: Ident, s: &mut Subst, id_gen: &IdGenerator) -> Ident {
        let renamed = id.rename(id_gen);
        let v = a.var(renamed);
        s.insert(id, v);
        renamed
    }
    let rw = |a: &mut LamArena, s: &mut Subst, x: Lam| rewrite_bounded_vars(a, s, x, id_gen);
    match a.node(lam) {
        Node::Var(id) => s.get(&a.ident(id)).copied().unwrap_or(lam),
        Node::Const(_) | Node::GlobalModule(_) => lam,
        Node::Apply { func, args, info } => {
            let func = rw(a, s, func);
            let args: smallvec::SmallVec<[Lam; 8]> =
                a.list_vec(args).into_iter().map(|x| rw(a, s, x)).collect();
            let p = a.apply_payload(info).clone();
            a.apply(func, &args, p.info)
        }
        Node::Function { body, info } => {
            let p = a.func_payload(info).clone();
            let params: smallvec::SmallVec<[Ident; 8]> = a
                .idents(p.params)
                .to_vec()
                .into_iter()
                .map(|x| rebind(a, x, s, id_gen))
                .collect();
            let body = rw(a, s, body);
            a.function_(p.arity, &params, body, p.attr, p.loc)
        }
        Node::Let {
            kind,
            id,
            value,
            body,
        } => {
            let id = rebind(a, a.ident(id), s, id_gen);
            let value = rw(a, s, value);
            let body = rw(a, s, body);
            a.let_(kind, id, value, body)
        }
        Node::LetRec { ids, values, body } => {
            let values = a.list_vec(values);
            let old: smallvec::SmallVec<[Ident; 8]> =
                a.ident_run(ids, values.len()).iter().copied().collect();
            let renamed: smallvec::SmallVec<[Ident; 8]> =
                old.into_iter().map(|x| rebind(a, x, s, id_gen)).collect();
            let bindings: smallvec::SmallVec<[(Ident, Lam); 8]> = renamed
                .into_iter()
                .zip(values)
                .map(|(id, x)| (id, rw(a, s, x)))
                .collect();
            let body = rw(a, s, body);
            a.letrec(&bindings, body)
        }
        Node::Prim { args, info } => {
            let args: smallvec::SmallVec<[Lam; 8]> =
                a.list_vec(args).into_iter().map(|x| rw(a, s, x)).collect();
            let args = a.add_list(&args);
            a.prim_with(info, args)
        }
        Node::Switch {
            scrut,
            actions,
            info,
        } => {
            let scrut = rw(a, s, scrut);
            let actions: smallvec::SmallVec<[Lam; 8]> = a
                .list_vec(actions)
                .into_iter()
                .map(|x| rw(a, s, x))
                .collect();
            let actions = a.add_list(&actions);
            a.switch_with(scrut, actions, info)
        }
        Node::StringSwitch {
            scrut,
            actions,
            info,
        } => {
            let scrut = rw(a, s, scrut);
            let actions: smallvec::SmallVec<[Lam; 8]> = a
                .list_vec(actions)
                .into_iter()
                .map(|x| rw(a, s, x))
                .collect();
            let actions = a.add_list(&actions);
            a.string_switch_with(scrut, actions, info)
        }
        Node::StaticRaise { label, args } => {
            let args: smallvec::SmallVec<[Lam; 8]> =
                a.list_vec(args).into_iter().map(|x| rw(a, s, x)).collect();
            a.static_raise(label, &args)
        }
        Node::StaticCatch {
            body,
            handler,
            info,
        } => {
            let body = rw(a, s, body);
            let p = a.catch_payload(info);
            let vars: smallvec::SmallVec<[Ident; 8]> = a
                .idents(p.params)
                .to_vec()
                .into_iter()
                .map(|x| rebind(a, x, s, id_gen))
                .collect();
            let handler = rw(a, s, handler);
            a.static_catch(body, p.label, &vars, handler)
        }
        Node::TryWith { body, id, handler } => {
            let body = rw(a, s, body);
            let exn = rebind(a, a.ident(id), s, id_gen);
            let handler = rw(a, s, handler);
            a.try_(body, exn, handler)
        }
        // lam_bounded_vars.ml: `let l1 = aux l1 in let l2 = aux l2 in try_finally l1 l2`.
        Node::TryFinally { body, finally } => {
            let body = rw(a, s, body);
            let finally = rw(a, s, finally);
            a.try_finally(body, finally)
        }
        Node::If { cond, then_, else_ } => {
            let cond = rw(a, s, cond);
            let then_ = rw(a, s, then_);
            let else_ = rw(a, s, else_);
            a.if_(cond, then_, else_)
        }
        Node::Sequence(x, y) => {
            let x = rw(a, s, x);
            let y = rw(a, s, y);
            a.seq(x, y)
        }
        Node::While(x, y) => {
            let x = rw(a, s, x);
            let y = rw(a, s, y);
            a.while_(x, y)
        }
        Node::For { dir, id, kids } => {
            let (from, to, body) = a.for_parts(kids);
            let id = rebind(a, a.ident(id), s, id_gen);
            let from = rw(a, s, from);
            let to = rw(a, s, to);
            let body = rw(a, s, body);
            // lam_bounded_vars.ml: `Lambda.for_ ident (aux l1) l2 dir l3`
            // rewrites the already rewritten start expression once more.
            let from = rw(a, s, from);
            a.for_(id, from, to, dir, body)
        }
        Node::ForOf { id, iter, body } => {
            let id = rebind(a, a.ident(id), s, id_gen);
            let iter = rw(a, s, iter);
            let body = rw(a, s, body);
            a.for_of(id, iter, body)
        }
        Node::ForAwaitOf { id, iter, body } => {
            let id = rebind(a, a.ident(id), s, id_gen);
            let iter = rw(a, s, iter);
            let body = rw(a, s, body);
            a.for_await_of(id, iter, body)
        }
        Node::Break | Node::Continue => lam,
        Node::Assign { id, value } => {
            let value = rw(a, s, value);
            a.assign_with(id, value)
        }
    }
}

/// The largest identifier stamp in `lam`.
#[cfg(test)]
pub(crate) fn max_ident_stamp_in_lambda(a: &LamArena, lam: Lam) -> i32 {
    let own = match a.node(lam) {
        Node::Var(id)
        | Node::GlobalModule(id)
        | Node::Let { id, .. }
        | Node::TryWith { id, .. }
        | Node::For { id, .. }
        | Node::ForOf { id, .. }
        | Node::ForAwaitOf { id, .. }
        | Node::Assign { id, .. } => a.ident(id).stamp(),
        Node::Function { info, .. } => a.params(info).iter().map(Ident::stamp).max().unwrap_or(0),
        Node::LetRec { ids, values, .. } => a
            .ident_run(ids, a.list_len(values))
            .iter()
            .map(Ident::stamp)
            .max()
            .unwrap_or(0),
        Node::StaticCatch { info, .. } => a
            .idents(a.catch_payload(info).params)
            .iter()
            .map(Ident::stamp)
            .max()
            .unwrap_or(0),
        _ => 0,
    };
    let mut max = own;
    a.iter_children(lam, |x| max = max.max(max_ident_stamp_in_lambda(a, x)));
    max
}

#[cfg(test)]
mod regression_tests {
    use super::*;
    use crate::ident::IdentFlags;
    fn ids(start: i32, count: usize) -> Vec<Ident> {
        (0..count)
            .map(|i| Ident::new(format!("p{i}"), start + i as i32, IdentFlags::NONE))
            .collect()
    }
    fn effect(name: &str) -> crate::lambda::Lambda {
        crate::lambda::Lambda::prim(
            Primitive::PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
                prim_name: name.into(),
                arg_types: vec![],
                ffi: crate::lambda::lam_primitive::ExternalDecl::test_val("", 0),
            })),
            vec![],
            LamLoc::NONE,
        )
    }
    fn prim(primitive: Primitive, args: Vec<crate::lambda::Lambda>) -> crate::lambda::Lambda {
        crate::lambda::Lambda::prim(primitive, args, LamLoc::NONE)
    }
    fn var(id: Ident) -> crate::lambda::Lambda {
        crate::lambda::Lambda::var(id)
    }
    /// `r.contents`: no side effects, but reads state that may change.
    fn read(r: Ident) -> crate::lambda::Lambda {
        prim(
            Primitive::Pfield(
                0,
                crate::lambda::lam_compat::FieldDbgInfo::Record {
                    name: crate::name::Name::new("contents"),
                },
            ),
            vec![var(r)],
        )
    }
    /// `simple_beta_reduce` of `(fun params -> body)(args)`, exported.
    fn reduce(
        params: &[Ident],
        body: crate::lambda::Lambda,
        args: Vec<crate::lambda::Lambda>,
    ) -> Option<crate::lambda::Lambda> {
        let mut store = LamArena::new();
        let root = store.import(&body);
        let args: Vec<_> = args.iter().map(|arg| store.import(arg)).collect();
        let reduced = simple_beta_reduce(&mut store, &AHashSet::new(), params, root, &args)?;
        Some(store.export(reduced))
    }
    #[test]
    fn unused_effectful_arguments_are_evaluated_in_parameter_order() {
        let params = ids(1, 3);
        let x = Ident::new("x".to_string(), 10, IdentFlags::NONE);
        let body = prim(Primitive::Pidentity, vec![var(params[0])]);
        let reduced = reduce(&params, body, vec![var(x), effect("b"), effect("c")])
            .expect("a variable runs anywhere");
        let mut names = Vec::new();
        let mut current = reduced;
        while let crate::lambda::Lambda::Lsequence(first, rest) = current {
            if let crate::lambda::Lambda::Lprim(info) = *first
                && let Primitive::PjsCall(call) = info.primitive
            {
                names.push(call.prim_name);
            }
            current = *rest;
        }
        assert_eq!(names, vec!["b", "c"]);
    }

    /// lam_beta_reduce_util.ml:25-40, rule 2: the body's use of the first
    /// argument would run it after the unused ones, so two arguments with
    /// side effects would swap.
    #[test]
    fn a_used_argument_with_effects_keeps_its_place_before_unused_ones() {
        let params = ids(1, 3);
        let body = prim(Primitive::Pidentity, vec![var(params[0])]);
        assert!(reduce(&params, body, vec![effect("a"), effect("b"), effect("c")]).is_none());
    }

    /// `(a, b) => b - a` applied to `(r.contents, bump())`: substituting
    /// would read `r` after `bump()` runs, and applied to `(bump(),
    /// r.contents)` before it. `(a, b) => a - b` keeps the call's order.
    #[test]
    fn a_read_does_not_move_past_an_effect() {
        let params = ids(1, 2);
        let r = Ident::new("r".to_string(), 10, IdentFlags::NONE);
        let swapped = prim(Primitive::Psubint, vec![var(params[1]), var(params[0])]);
        let in_order = prim(Primitive::Psubint, vec![var(params[0]), var(params[1])]);
        assert!(reduce(&params, swapped.clone(), vec![read(r), effect("bump")]).is_none());
        assert!(reduce(&params, swapped.clone(), vec![effect("bump"), read(r)]).is_none());
        assert!(reduce(&params, swapped, vec![read(r), read(r)]).is_some());
        assert!(reduce(&params, in_order.clone(), vec![read(r), effect("bump")]).is_some());
        assert!(reduce(&params, in_order, vec![effect("bump"), read(r)]).is_some());
    }

    /// lam_beta_reduce_util.ml:25-40, rule 3: an argument with side effects
    /// never goes to the right operand of `&&`, which may not run.
    #[test]
    fn an_effect_does_not_go_to_the_right_of_and() {
        let params = ids(1, 2);
        let x = Ident::new("x".to_string(), 10, IdentFlags::NONE);
        let body = prim(Primitive::Psequand, vec![var(params[0]), var(params[1])]);
        assert!(reduce(&params, body.clone(), vec![var(x), effect("f")]).is_none());
        assert!(reduce(&params, body, vec![effect("f"), var(x)]).is_some());
    }
}
