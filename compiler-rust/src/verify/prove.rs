//! Proofs of laws (docs/verify/proof.md).
//!
//! `rescript verify` runs a law on values. This module tries to show that
//! the law is true for every value, by reasoning about the law's code
//! instead of running it:
//!
//! - the law is evaluated with unknowns for its parameters;
//! - where the code takes an unknown apart (`switch`, `if`), the proof
//!   splits into one case per constructor;
//! - an unknown of a recursive type is split by structural induction: the
//!   law may be used for the parts of the value;
//! - laws proved earlier in the file are used as rewrite rules;
//! - `int` arithmetic is compared as polynomials modulo 2^32, which is what
//!   `+`, `-` and `*` compute, and `<=` facts are closed under transitivity.
//!
//! A proof must hold for the program as it runs, so the prover only reads
//! code whose meaning it knows exactly: total functions of this file over
//! `int`, `bool`, `string`, tuples, records, variants, options and lists.
//! A recursive function must recurse on a part of one argument, which makes
//! it total. Anything else (floats, exceptions, functions of other files)
//! ends the attempt, and the law is run on values as before.

use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use serde_json::{Value, json};

use super::purity::Index;
use super::shape::{self, Definitions};
use crate::parser::ast::RecFlag;
use crate::types::asttypes::ArgLabel;
use crate::types::context::TypeContext;
use crate::types::decl::{ConstructorKind, ValueKind};
use crate::types::path::PathView;
use crate::types::type_expr::TypeDesc;
use crate::types::typedtree::*;
use crate::types::{TypeExprRef, predef};

/// A law that was proved: later laws of the file may use it.
pub(super) struct Lemma {
    pub name: String,
    pub expr: TExprIdx,
    pub shapes: Vec<Value>,
}

/// A value the prover reasons about. Terms are kept in normal form: built
/// only by the `mk_*` functions.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Term {
    /// An unknown value.
    Var(u32),
    Int(i32),
    Str(String),
    /// A constructor, a tuple (`(,)`) or a record (`{}`) of known parts.
    Ctor(String, Vec<Term>),
    /// A call of a recursive function that cannot be computed further.
    App(i32, Vec<Term>),
    /// A polynomial over `int` terms: products with coefficients, and a
    /// constant. Never a constant alone or a single term.
    Sum(Vec<(Vec<Term>, i32)>, i32),
    Prim(Op, Vec<Term>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Op {
    Le,
    Eq,
    Not,
    And,
    Or,
    Div,
    Mod,
    Concat,
}

fn truth(value: bool) -> Term {
    Term::Ctor(if value { "true" } else { "false" }.to_string(), Vec::new())
}

fn is(term: &Term, value: bool) -> bool {
    matches!(term, Term::Ctor(name, _) if name == if value { "true" } else { "false" })
}

/// Why an evaluation stopped.
enum Halt {
    /// The code takes this term apart and its constructor is not known; the
    /// shape is that of its type.
    Stuck(Term, Value),
    /// The code does something the prover does not read.
    Unsupported(String),
    /// The step budget ran out.
    Fuel,
}

type Res<T> = Result<T, Halt>;

fn unsupported<T>(what: impl Into<String>) -> Res<T> {
    Err(Halt::Unsupported(what.into()))
}

#[derive(Clone)]
enum Val {
    Term(Term),
    Fun(Rc<Closure>),
    Prim(String),
}

struct Closure {
    params: TParamList,
    body: TExprIdx,
    env: Env,
    /// The top-level binding this function is, when it is one.
    global: Option<i32>,
}

type Env = Option<Rc<Node>>;

struct Node {
    stamp: i32,
    val: Val,
    next: Env,
}

fn bind(env: Env, stamp: i32, val: Val) -> Env {
    Some(Rc::new(Node {
        stamp,
        val,
        next: env,
    }))
}

fn lookup(mut env: &Env, stamp: i32) -> Option<Val> {
    while let Some(node) = env {
        if node.stamp == stamp {
            return Some(node.val.clone());
        }
        env = &node.next;
    }
    None
}

/// What is known about a top-level function.
#[derive(Clone, Copy)]
enum FnInfo {
    /// Not recursive: calls are replaced by the body.
    Plain,
    /// Recursive on a part of the argument at this position.
    Rec(usize),
    /// Recursive in a way that is not known to end.
    Bad,
}

#[derive(Clone, PartialEq)]
enum Kind {
    /// A law proved earlier, by name.
    Lemma(String),
    /// The law itself, for a part of a value (induction).
    Hypothesis,
    /// What a case of the proof assumes.
    Fact,
}

/// `lhs` may be replaced by `rhs`; the variables of `pats` stand for any
/// term.
struct Rule {
    lhs: Term,
    rhs: Term,
    pats: Vec<u32>,
    kind: Kind,
    /// Both sides have one form (`f(a, b) == f(b, a)`): only applied when
    /// the result is smaller, so that it ends.
    ordered: bool,
}

enum Split {
    Var(u32),
    Term(Term, Value),
}

/// A polynomial with coefficients modulo 2^32; the empty product is the
/// constant.
struct Poly(BTreeMap<Vec<Term>, i32>);

impl Poly {
    fn of(term: &Term) -> Poly {
        let mut map = BTreeMap::new();
        match term {
            Term::Int(n) => {
                map.insert(Vec::new(), *n);
            }
            Term::Sum(terms, constant) => {
                map.insert(Vec::new(), *constant);
                for (product, coefficient) in terms {
                    map.insert(product.clone(), *coefficient);
                }
            }
            other => {
                map.insert(vec![other.clone()], 1);
            }
        }
        Poly(map)
    }

    fn add(mut self, other: &Poly, sign: i32) -> Poly {
        for (product, coefficient) in &other.0 {
            let entry = self.0.entry(product.clone()).or_insert(0);
            *entry = entry.wrapping_add(coefficient.wrapping_mul(sign));
        }
        self
    }

    fn mul(&self, other: &Poly) -> Poly {
        let mut map: BTreeMap<Vec<Term>, i32> = BTreeMap::new();
        for (a, x) in &self.0 {
            for (b, y) in &other.0 {
                let mut product = a.clone();
                product.extend(b.iter().cloned());
                product.sort();
                let entry = map.entry(product).or_insert(0);
                *entry = entry.wrapping_add(x.wrapping_mul(*y));
            }
        }
        Poly(map)
    }

    fn constant(&self) -> Option<i32> {
        self.0
            .iter()
            .all(|(product, coefficient)| product.is_empty() || *coefficient == 0)
            .then(|| self.0.get(&Vec::new()).copied().unwrap_or(0))
    }

    fn term(mut self) -> Term {
        self.0
            .retain(|product, coefficient| product.is_empty() || *coefficient != 0);
        let constant = self.0.remove(&Vec::new()).unwrap_or(0);
        if self.0.is_empty() {
            return Term::Int(constant);
        }
        if constant == 0 && self.0.len() == 1 {
            let (product, coefficient) = self.0.iter().next().expect("one product");
            if *coefficient == 1 && product.len() == 1 {
                return product[0].clone();
            }
        }
        Term::Sum(self.0.into_iter().collect(), constant)
    }
}

fn subst(term: &Term, var: u32, with: &Term) -> Term {
    let again = |parts: &[Term]| parts.iter().map(|part| subst(part, var, with)).collect();
    match term {
        Term::Var(v) if *v == var => with.clone(),
        Term::Var(_) | Term::Int(_) | Term::Str(_) => term.clone(),
        Term::Ctor(name, args) => Term::Ctor(name.clone(), again(args)),
        Term::App(f, args) => Term::App(*f, again(args)),
        Term::Prim(op, args) => Term::Prim(*op, again(args)),
        Term::Sum(terms, constant) => Term::Sum(
            terms
                .iter()
                .map(|(product, c)| (again(product), *c))
                .collect(),
            *constant,
        ),
    }
}

fn vars(term: &Term, out: &mut Vec<u32>) {
    match term {
        Term::Var(v) => {
            if !out.contains(v) {
                out.push(*v);
            }
        }
        Term::Int(_) | Term::Str(_) => {}
        Term::Ctor(_, args) | Term::App(_, args) | Term::Prim(_, args) => {
            args.iter().for_each(|arg| vars(arg, out));
        }
        Term::Sum(terms, _) => terms
            .iter()
            .flat_map(|(product, _)| product)
            .for_each(|t| vars(t, out)),
    }
}

/// Whether `term` is an instance of `pattern`, with the terms its pattern
/// variables stand for.
fn matches(pattern: &Term, term: &Term, pats: &[u32], found: &mut HashMap<u32, Term>) -> bool {
    let all = |xs: &[Term], ys: &[Term], found: &mut HashMap<u32, Term>| {
        xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| matches(x, y, pats, found))
    };
    match (pattern, term) {
        (Term::Var(p), _) if pats.contains(p) => match found.get(p) {
            Some(known) => known == term,
            None => {
                found.insert(*p, term.clone());
                true
            }
        },
        (Term::Ctor(n, xs), Term::Ctor(m, ys)) => n == m && all(xs, ys, found),
        (Term::App(f, xs), Term::App(g, ys)) => f == g && all(xs, ys, found),
        (Term::Prim(o, xs), Term::Prim(p, ys)) => o == p && all(xs, ys, found),
        _ => pattern == term,
    }
}

/// `term` with every pattern variable replaced at once: what a variable
/// stands for may itself have variables of the same names.
fn instance(term: &Term, found: &HashMap<u32, Term>) -> Term {
    let again = |parts: &[Term]| parts.iter().map(|part| instance(part, found)).collect();
    match term {
        Term::Var(v) => found.get(v).cloned().unwrap_or_else(|| term.clone()),
        Term::Int(_) | Term::Str(_) => term.clone(),
        Term::Ctor(name, args) => Term::Ctor(name.clone(), again(args)),
        Term::App(f, args) => Term::App(*f, again(args)),
        Term::Prim(op, args) => Term::Prim(*op, again(args)),
        Term::Sum(terms, constant) => Term::Sum(
            terms
                .iter()
                .map(|(product, c)| (again(product), *c))
                .collect(),
            *constant,
        ),
    }
}

fn mentions(rule: &Rule, var: u32) -> bool {
    let mut found = Vec::new();
    vars(&rule.lhs, &mut found);
    vars(&rule.rhs, &mut found);
    found.contains(&var) && !rule.pats.contains(&var)
}

struct Prover<'a> {
    ctx: &'a TypeContext,
    ta: &'a TypedArena,
    index: &'a Index,
    defs: Definitions,
    fns: HashMap<i32, FnInfo>,
    rules: Vec<Rc<Rule>>,
    var_shapes: Vec<Value>,
    /// The parameter each unknown is, or is a part of.
    var_names: Vec<String>,
    steps: u32,
    depth: u32,
    cases: u32,
    /// The cases that were shown to be true.
    shown: u32,
    inductions: Vec<String>,
    used: Vec<String>,
}

const STEPS: u32 = 400_000;
const DEPTH: u32 = 120;
const CASES: u32 = 4_000;
const SPLITS: u32 = 16;

impl<'a> Prover<'a> {
    fn tick(&mut self) -> Res<()> {
        self.steps += 1;
        if self.steps > STEPS {
            Err(Halt::Fuel)
        } else {
            Ok(())
        }
    }

    fn fresh(&mut self, shape: Value, name: &str) -> Term {
        self.var_shapes.push(shape);
        self.var_names.push(name.to_string());
        Term::Var(self.var_shapes.len() as u32 - 1)
    }

    fn shape(&mut self, ty: TypeExprRef, env: EnvRef) -> Res<Value> {
        let Some(env) = self.ctx.get_typed_env(env) else {
            return unsupported("it has a value whose type is not known here");
        };
        shape::of_type(self.ctx, &env, ty, &mut self.defs).map_err(|shape::Unsupported(why)| {
            Halt::Unsupported(format!("it takes apart a value that cannot be: {why}"))
        })
    }

    fn stuck<T>(&mut self, term: &Term, ty: TypeExprRef, env: EnvRef) -> Res<T> {
        let shape = self.shape(ty, env)?;
        Err(Halt::Stuck(term.clone(), shape))
    }

    fn is_type(&self, ty: TypeExprRef, env: EnvRef, wanted: &[crate::types::Path]) -> bool {
        let Some(env) = self.ctx.get_typed_env(env) else {
            return false;
        };
        let ty = crate::types::ctype::expand_head(self.ctx, &env, ty);
        matches!(
            &*self.ctx.borrow_desc(self.ctx.repr(ty)),
            TypeDesc::Tconstr { path, .. } if wanted.iter().any(|w| path.same(w))
        )
    }

    fn need_int(&self, expr: TExprIdx) -> Res<()> {
        let e = self.ta.expr(expr);
        if self.is_type(e.exp_type, e.exp_env, &[predef::path_int()]) {
            Ok(())
        } else {
            unsupported("it computes with numbers that are not `int`")
        }
    }

    // --- Terms ------------------------------------------------------------

    fn rewrite(&mut self, term: Term) -> Res<Term> {
        for at in 0..self.rules.len() {
            let rule = self.rules[at].clone();
            let mut found = HashMap::new();
            if !matches(&rule.lhs, &term, &rule.pats, &mut found) {
                continue;
            }
            let out = instance(&rule.rhs, &found);
            if rule.ordered && out >= term {
                continue;
            }
            self.tick()?;
            if let Kind::Lemma(name) = &rule.kind
                && !self.used.contains(name)
            {
                self.used.push(name.clone());
            }
            if self.depth > DEPTH {
                return Err(Halt::Fuel);
            }
            self.depth += 1;
            let out = self.renorm(&out);
            self.depth -= 1;
            return out;
        }
        Ok(term)
    }

    /// The normal form of a term built outside the `mk_*` functions.
    fn renorm(&mut self, term: &Term) -> Res<Term> {
        self.tick()?;
        let parts = |this: &mut Self, args: &[Term]| -> Res<Vec<Term>> {
            args.iter().map(|arg| this.renorm(arg)).collect()
        };
        match term {
            Term::Var(_) | Term::Int(_) | Term::Str(_) => Ok(term.clone()),
            Term::Ctor(name, args) => {
                let args = parts(self, args)?;
                self.rewrite(Term::Ctor(name.clone(), args))
            }
            Term::App(f, args) => {
                let args = parts(self, args)?;
                self.mk_app(*f, args)
            }
            Term::Sum(terms, constant) => {
                let mut sum = Poly::of(&Term::Int(*constant));
                for (product, coefficient) in terms {
                    let mut value = Poly::of(&Term::Int(*coefficient));
                    for factor in parts(self, product)? {
                        value = value.mul(&Poly::of(&factor));
                    }
                    sum = sum.add(&value, 1);
                }
                Ok(sum.term())
            }
            Term::Prim(op, args) => {
                let mut args = parts(self, args)?;
                match op {
                    Op::Concat => self.mk_concat(args),
                    Op::Not => self.mk_not(args.remove(0)),
                    _ => {
                        let b = args.remove(1);
                        let a = args.remove(0);
                        match op {
                            Op::Le => self.mk_le(a, b),
                            Op::Eq => self.mk_eq(a, b),
                            Op::And => self.mk_and(a, b),
                            Op::Or => self.mk_or(a, b),
                            _ => self.mk_div(*op, a, b),
                        }
                    }
                }
            }
        }
    }

    fn mk_not(&mut self, a: Term) -> Res<Term> {
        if is(&a, true) || is(&a, false) {
            return Ok(truth(is(&a, false)));
        }
        if let Term::Prim(Op::Not, inner) = &a {
            return Ok(inner[0].clone());
        }
        self.rewrite(Term::Prim(Op::Not, vec![a]))
    }

    fn mk_and(&mut self, a: Term, b: Term) -> Res<Term> {
        if is(&a, false) || is(&b, false) {
            return Ok(truth(false));
        }
        if is(&a, true) || a == b {
            return Ok(b);
        }
        if is(&b, true) {
            return Ok(a);
        }
        self.rewrite(Term::Prim(Op::And, vec![a, b]))
    }

    fn mk_or(&mut self, a: Term, b: Term) -> Res<Term> {
        if is(&a, true) || is(&b, true) {
            return Ok(truth(true));
        }
        if is(&a, false) || a == b {
            return Ok(b);
        }
        if is(&b, false) {
            return Ok(a);
        }
        self.rewrite(Term::Prim(Op::Or, vec![a, b]))
    }

    fn mk_eq(&mut self, a: Term, b: Term) -> Res<Term> {
        // No float is ever a term, so a value equals itself.
        if a == b {
            return Ok(truth(true));
        }
        match (&a, &b) {
            (Term::Str(_), Term::Str(_)) => return Ok(truth(false)),
            (Term::Ctor(n, xs), Term::Ctor(m, ys)) => {
                if n != m || xs.len() != ys.len() {
                    return Ok(truth(false));
                }
                let mut all = truth(true);
                for (x, y) in xs.clone().into_iter().zip(ys.clone()) {
                    let equal = self.mk_eq(x, y)?;
                    all = self.mk_and(all, equal)?;
                }
                return Ok(all);
            }
            _ => {}
        }
        let number = |t: &Term| matches!(t, Term::Int(_) | Term::Sum(..));
        if (number(&a) || number(&b))
            && let Some(difference) = Poly::of(&a).add(&Poly::of(&b), -1).constant()
        {
            return Ok(truth(difference == 0));
        }
        let (a, b) = if a <= b { (a, b) } else { (b, a) };
        self.rewrite(Term::Prim(Op::Eq, vec![a, b]))
    }

    fn mk_le(&mut self, a: Term, b: Term) -> Res<Term> {
        if a == b {
            return Ok(truth(true));
        }
        if let (Term::Int(x), Term::Int(y)) = (&a, &b) {
            return Ok(truth(x <= y));
        }
        if let Some(known) = self.order(&a, &b) {
            return Ok(truth(known));
        }
        self.rewrite(Term::Prim(Op::Le, vec![a, b]))
    }

    /// `a <= b` as it follows from the `<=` facts of this case: `int` is a
    /// total order.
    fn order(&self, a: &Term, b: &Term) -> Option<bool> {
        // (from, to, strict): from <= to, or from < to.
        let mut edges: Vec<(&Term, &Term, bool)> = Vec::new();
        for rule in &self.rules {
            if let (Kind::Fact, Term::Prim(Op::Le, xy)) = (&rule.kind, &rule.lhs) {
                if is(&rule.rhs, true) {
                    edges.push((&xy[0], &xy[1], false));
                } else if is(&rule.rhs, false) {
                    edges.push((&xy[1], &xy[0], true));
                }
            }
        }
        if edges.is_empty() {
            return None;
        }
        // Whether `to` is reached from `from`, and whether strictly.
        let reach = |from: &Term, to: &Term| -> Option<bool> {
            let mut seen: Vec<(&Term, bool)> = vec![(from, false)];
            let mut at = 0;
            let mut best = None;
            while at < seen.len() {
                let (node, strict) = seen[at];
                at += 1;
                if node == to {
                    best = Some(strict || best == Some(true));
                }
                for (x, y, edge) in &edges {
                    let next = (*y, strict || *edge);
                    if *x == node && !seen.contains(&next) {
                        seen.push(next);
                    }
                }
            }
            best
        };
        if reach(a, b).is_some() {
            Some(true)
        } else if reach(b, a) == Some(true) {
            Some(false)
        } else {
            None
        }
    }

    fn mk_div(&mut self, op: Op, a: Term, b: Term) -> Res<Term> {
        if let (Term::Int(x), Term::Int(y)) = (&a, &b)
            && *y != 0
        {
            return Ok(Term::Int(if op == Op::Div {
                x.wrapping_div(*y)
            } else {
                x.wrapping_rem(*y)
            }));
        }
        self.rewrite(Term::Prim(op, vec![a, b]))
    }

    fn mk_concat(&mut self, parts: Vec<Term>) -> Res<Term> {
        let mut flat: Vec<Term> = Vec::new();
        for part in parts {
            let pieces = match part {
                Term::Prim(Op::Concat, inner) => inner,
                other => vec![other],
            };
            for piece in pieces {
                match (flat.last_mut(), piece) {
                    (_, Term::Str(text)) if text.is_empty() => {}
                    (Some(Term::Str(last)), Term::Str(text)) => last.push_str(&text),
                    (_, piece) => flat.push(piece),
                }
            }
        }
        match flat.len() {
            0 => Ok(Term::Str(String::new())),
            1 => Ok(flat.remove(0)),
            _ => self.rewrite(Term::Prim(Op::Concat, flat)),
        }
    }

    fn mk_app(&mut self, f: i32, args: Vec<Term>) -> Res<Term> {
        if let Some(FnInfo::Rec(position)) = self.fns.get(&f).copied()
            && matches!(args[position], Term::Ctor(..))
        {
            match self.unfold(f, &args) {
                Ok(term) => return Ok(term),
                Err(Halt::Stuck(..)) => {}
                Err(halt) => return Err(halt),
            }
        }
        self.rewrite(Term::App(f, args))
    }

    fn unfold(&mut self, f: i32, args: &[Term]) -> Res<Term> {
        let Val::Fun(closure) = self.global(f)? else {
            return unsupported("it calls a value that is not a function");
        };
        match self.call(&closure, args.iter().cloned().map(Val::Term).collect())? {
            Val::Term(term) => Ok(term),
            _ => unsupported("it has a function that returns a function"),
        }
    }

    // --- Code -------------------------------------------------------------

    fn global(&mut self, stamp: i32) -> Res<Val> {
        let Some((expr, _)) = self.index.definition(stamp) else {
            return unsupported("it uses a value the prover cannot find");
        };
        match &self.ta.expr(expr).exp_desc {
            ExpressionDesc::Texp_function {
                params,
                body,
                async_: false,
            } => Ok(Val::Fun(Rc::new(Closure {
                params: *params,
                body: *body,
                env: None,
                global: Some(stamp),
            }))),
            _ => self.eval(expr, &None),
        }
    }

    fn info(&mut self, stamp: i32, closure: &Closure) -> FnInfo {
        if let Some(info) = self.fns.get(&stamp) {
            return *info;
        }
        let info = structural(
            self.ta,
            stamp,
            self.ta.function_params(closure.params),
            closure.body,
        );
        self.fns.insert(stamp, info);
        info
    }

    fn call(&mut self, closure: &Closure, args: Vec<Val>) -> Res<Val> {
        self.tick()?;
        if self.depth > DEPTH {
            return Err(Halt::Fuel);
        }
        let params = self.ta.function_params(closure.params);
        if params.len() != args.len() {
            return unsupported("it applies a function to some of its arguments only");
        }
        let mut env = closure.env.clone();
        for (param, arg) in params.iter().zip(args) {
            if !matches!(param.fp_lbl, ArgLabel::Nolabel) {
                return unsupported("it calls a function with labelled arguments");
            }
            env = bind(env, param.fp_param.stamp(), arg.clone());
            env = self.bind_val(env, param.fp_pat, arg)?;
        }
        self.depth += 1;
        let result = self.eval(closure.body, &env);
        self.depth -= 1;
        result
    }

    fn bind_val(&mut self, env: Env, pat: TPatIdx, val: Val) -> Res<Env> {
        match (&self.ta.pattern(pat).pat_desc, val) {
            (PatternDesc::Tpat_any, _) => Ok(env),
            (PatternDesc::Tpat_var(id, _), val) => Ok(bind(env, id.stamp(), val)),
            (PatternDesc::Tpat_alias(inner, id, _), val) => {
                let env = bind(env, id.stamp(), val.clone());
                self.bind_val(env, *inner, val)
            }
            (_, Val::Term(term)) => {
                let mut env = env;
                if self.match_pat(&term, pat, &mut env)? {
                    Ok(env)
                } else {
                    unsupported("it has a `let` whose pattern can fail")
                }
            }
            _ => unsupported("it takes a function apart"),
        }
    }

    /// Whether a term matches a pattern, binding its names.
    fn match_pat(&mut self, term: &Term, pat: TPatIdx, env: &mut Env) -> Res<bool> {
        let ta = self.ta;
        let pattern = ta.pattern(pat);
        match &pattern.pat_desc {
            PatternDesc::Tpat_any => Ok(true),
            PatternDesc::Tpat_var(id, _) => {
                *env = bind(env.take(), id.stamp(), Val::Term(term.clone()));
                Ok(true)
            }
            PatternDesc::Tpat_alias(inner, id, _) => {
                *env = bind(env.take(), id.stamp(), Val::Term(term.clone()));
                self.match_pat(term, *inner, env)
            }
            PatternDesc::Tpat_constant(constant) => {
                let literal = literal(constant)?;
                let equal = self.mk_eq(term.clone(), literal)?;
                if is(&equal, true) || is(&equal, false) {
                    Ok(is(&equal, true))
                } else {
                    Err(Halt::Stuck(equal, json!({ "k": "bool" })))
                }
            }
            PatternDesc::Tpat_tuple(parts) => {
                self.match_parts(term, "(,)", ta.pattern_list(*parts), pattern, env)
            }
            PatternDesc::Tpat_construct(_, constructor, parts) => {
                if constructor.cstr_inlined.is_some()
                    || !matches!(constructor.cstr_kind, ConstructorKind::Ordinary(_))
                {
                    return unsupported(
                        "it uses a constructor with an inline record, or an exception",
                    );
                }
                self.match_parts(
                    term,
                    &constructor.cstr_name,
                    ta.pattern_list(*parts),
                    pattern,
                    env,
                )
            }
            PatternDesc::Tpat_record(fields, _, None) => match term {
                Term::Ctor(name, args) if name == "{}" => {
                    for (_, label, part, _) in fields {
                        if !self.match_pat(&args[label.lbl_pos as usize], *part, env)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                }
                _ => self.stuck(term, pattern.pat_type, pattern.pat_env),
            },
            PatternDesc::Tpat_or(left, right, _) => {
                Ok(self.match_pat(term, *left, env)? || self.match_pat(term, *right, env)?)
            }
            _ => unsupported("it has a pattern the prover does not read"),
        }
    }

    fn match_parts(
        &mut self,
        term: &Term,
        name: &str,
        parts: &[TPatIdx],
        pattern: &Pattern,
        env: &mut Env,
    ) -> Res<bool> {
        match term {
            Term::Ctor(found, args) => {
                if found != name {
                    return Ok(false);
                }
                if args.len() != parts.len() {
                    return unsupported("it has a pattern the prover does not read");
                }
                for (arg, part) in args.iter().zip(parts) {
                    if !self.match_pat(arg, *part, env)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => self.stuck(term, pattern.pat_type, pattern.pat_env),
        }
    }

    fn term(&mut self, expr: TExprIdx, env: &Env) -> Res<Term> {
        match self.eval(expr, env)? {
            Val::Term(term) => Ok(term),
            _ => unsupported("it uses a function as a value"),
        }
    }

    fn terms(&mut self, exprs: &[TExprIdx], env: &Env) -> Res<Vec<Term>> {
        exprs.iter().map(|expr| self.term(*expr, env)).collect()
    }

    fn eval(&mut self, idx: TExprIdx, env: &Env) -> Res<Val> {
        self.tick()?;
        let ta = self.ta;
        let e = ta.expr(idx);
        match &e.exp_desc {
            ExpressionDesc::Texp_ident(path, _, description) => {
                if let PathView::Pident(id) = path.view()
                    && let Some(val) = lookup(env, id.stamp())
                {
                    return Ok(val);
                }
                if let ValueKind::ValPrim(primitive) = &description.val_kind {
                    return Ok(Val::Prim(primitive.prim_name.clone()));
                }
                match self.index.resolve(path) {
                    Some(stamp) => self.global(stamp),
                    None => unsupported(format!(
                        "it uses `{}`, which is defined in another file",
                        path.name()
                            .trim_start_matches("Stdlib_")
                            .trim_start_matches("Stdlib.")
                    )),
                }
            }
            ExpressionDesc::Texp_constant(constant) => literal(constant).map(Val::Term),
            ExpressionDesc::Texp_let(recursive, bindings, body) => {
                if matches!(recursive, RecFlag::Recursive) {
                    return unsupported("it defines a recursive function inside another function");
                }
                let mut inner = env.clone();
                for binding in ta.value_bindings(*bindings) {
                    let val = self.eval(binding.vb_expr, env)?;
                    inner = self.bind_val(inner, binding.vb_pat, val)?;
                }
                self.eval(*body, &inner)
            }
            ExpressionDesc::Texp_function {
                params,
                body,
                async_: false,
            } => Ok(Val::Fun(Rc::new(Closure {
                params: *params,
                body: *body,
                env: env.clone(),
                global: None,
            }))),
            ExpressionDesc::Texp_apply {
                funct,
                args,
                partial: false,
                ..
            } => {
                let function = self.eval(*funct, env)?;
                let mut exprs = Vec::new();
                for arg in ta.apply_args(*args) {
                    match (&arg.label, arg.expression) {
                        (ArgLabel::Nolabel, Some(expr)) => exprs.push(expr),
                        _ => return unsupported("it calls a function with labelled arguments"),
                    }
                }
                match function {
                    Val::Prim(name) => self.primitive(&name, &exprs, idx, env).map(Val::Term),
                    Val::Fun(closure) => {
                        let mut args = Vec::new();
                        for expr in &exprs {
                            args.push(self.eval(*expr, env)?);
                        }
                        let Some(stamp) = closure.global else {
                            return self.call(&closure, args);
                        };
                        match self.info(stamp, &closure) {
                            FnInfo::Plain => self.call(&closure, args),
                            FnInfo::Bad => unsupported(format!(
                                "`{}` is recursive, and not on a part of one of its arguments",
                                self.index
                                    .definition(stamp)
                                    .map_or("a function", |(_, name)| name)
                            )),
                            FnInfo::Rec(_) => {
                                let mut terms = Vec::new();
                                for arg in args {
                                    match arg {
                                        Val::Term(term) => terms.push(term),
                                        _ => {
                                            return unsupported(
                                                "it passes a function to a recursive function",
                                            );
                                        }
                                    }
                                }
                                if terms.len() != ta.function_params(closure.params).len() {
                                    return unsupported(
                                        "it applies a function to some of its arguments only",
                                    );
                                }
                                self.mk_app(stamp, terms).map(Val::Term)
                            }
                        }
                    }
                    Val::Term(_) => {
                        unsupported("it calls a value that is not a function of this file")
                    }
                }
            }
            ExpressionDesc::Texp_match(scrutinee, cases, exceptions, _) => {
                if !ta.cases(*exceptions).is_empty() {
                    return unsupported("it handles exceptions");
                }
                let term = self.term(*scrutinee, env)?;
                for case in ta.cases(*cases) {
                    if case.c_guard.is_some() {
                        return unsupported("it has a `switch` case with a `when`");
                    }
                    let mut inner = env.clone();
                    if self.match_pat(&term, case.c_lhs, &mut inner)? {
                        return self.eval(case.c_rhs, &inner);
                    }
                }
                unsupported("it has a `switch` that does not cover every value")
            }
            ExpressionDesc::Texp_tuple(parts) => {
                let args = self.terms(ta.expr_list(*parts), env)?;
                self.rewrite(Term::Ctor("(,)".to_string(), args))
                    .map(Val::Term)
            }
            ExpressionDesc::Texp_construct(_, constructor, args) => {
                if constructor.cstr_inlined.is_some()
                    || !matches!(constructor.cstr_kind, ConstructorKind::Ordinary(_))
                {
                    return unsupported(
                        "it uses a constructor with an inline record, or an exception",
                    );
                }
                let args = self.terms(ta.expr_list(*args), env)?;
                self.rewrite(Term::Ctor(constructor.cstr_name.clone(), args))
                    .map(Val::Term)
            }
            ExpressionDesc::Texp_record {
                fields,
                extended_expression,
                ..
            } => {
                let fields = ta.record_fields(*fields);
                let Some(labels) = record_all_labels(self.ctx, fields) else {
                    return unsupported("it has an empty record");
                };
                if labels.iter().any(|label| label.lbl_optional) {
                    return unsupported("it has a record with optional fields");
                }
                let mut args: Vec<Option<Term>> = vec![None; labels.len()];
                if let Some(base) = extended_expression {
                    match self.term(*base, env)? {
                        Term::Ctor(name, known) if name == "{}" => {
                            args = known.into_iter().map(Some).collect()
                        }
                        other => {
                            let base = ta.expr(*base);
                            return self.stuck(&other, base.exp_type, base.exp_env);
                        }
                    }
                }
                for (label, _, expr) in fields {
                    args[label.lbl_pos as usize] = Some(self.term(*expr, env)?);
                }
                let Some(args) = args.into_iter().collect::<Option<Vec<Term>>>() else {
                    return unsupported("it has a record with fields left out");
                };
                self.rewrite(Term::Ctor("{}".to_string(), args))
                    .map(Val::Term)
            }
            ExpressionDesc::Texp_field(record, _, label) => match self.term(*record, env)? {
                Term::Ctor(name, args) if name == "{}" => {
                    Ok(Val::Term(args[label.lbl_pos as usize].clone()))
                }
                other => {
                    let record = ta.expr(*record);
                    self.stuck(&other, record.exp_type, record.exp_env)
                }
            },
            ExpressionDesc::Texp_ifthenelse(condition, then, Some(otherwise)) => {
                let condition = self.term(*condition, env)?;
                if is(&condition, true) {
                    self.eval(*then, env)
                } else if is(&condition, false) {
                    self.eval(*otherwise, env)
                } else {
                    Err(Halt::Stuck(condition, json!({ "k": "bool" })))
                }
            }
            ExpressionDesc::Texp_sequence(first, second) => {
                self.eval(*first, env)?;
                self.eval(*second, env)
            }
            _ => unsupported("it has an expression the prover does not read"),
        }
    }

    fn primitive(
        &mut self,
        name: &str,
        exprs: &[TExprIdx],
        call: TExprIdx,
        env: &Env,
    ) -> Res<Term> {
        if let ("%sequand" | "%sequor", [left, right]) = (name, exprs) {
            let and = name == "%sequand";
            let a = self.term(*left, env)?;
            if is(&a, !and) {
                return Ok(a);
            }
            let b = self.term(*right, env)?;
            return if and {
                self.mk_and(a, b)
            } else {
                self.mk_or(a, b)
            };
        }
        let mut args = self.terms(exprs, env)?;
        let scalar = [
            predef::path_int(),
            predef::path_bool(),
            predef::path_string(),
        ];
        match (name, args.len()) {
            ("%identity", 1) => Ok(args.remove(0)),
            ("%boolnot", 1) => self.mk_not(args.remove(0)),
            ("%neg", 1) => {
                self.need_int(call)?;
                Ok(Poly::of(&Term::Int(0)).add(&Poly::of(&args[0]), -1).term())
            }
            ("%string_concat", 2) => self.mk_concat(args),
            (_, 2) => {
                let b = args.remove(1);
                let a = args.remove(0);
                match name {
                    "%equal" => self.mk_eq(a, b),
                    "%notequal" => {
                        let equal = self.mk_eq(a, b)?;
                        self.mk_not(equal)
                    }
                    "%eq" | "%noteq" => {
                        let left = self.ta.expr(exprs[0]);
                        if !self.is_type(left.exp_type, left.exp_env, &scalar) {
                            return unsupported("it compares values with `===`");
                        }
                        let equal = self.mk_eq(a, b)?;
                        if name == "%eq" {
                            Ok(equal)
                        } else {
                            self.mk_not(equal)
                        }
                    }
                    "%add" | "%sub" => {
                        self.need_int(call)?;
                        Ok(Poly::of(&a)
                            .add(&Poly::of(&b), if name == "%add" { 1 } else { -1 })
                            .term())
                    }
                    "%mul" => {
                        self.need_int(call)?;
                        Ok(Poly::of(&a).mul(&Poly::of(&b)).term())
                    }
                    "%div" | "%mod" => {
                        self.need_int(call)?;
                        if !matches!(b, Term::Int(n) if n != 0) {
                            return unsupported("it divides by a number that could be zero");
                        }
                        self.mk_div(if name == "%div" { Op::Div } else { Op::Mod }, a, b)
                    }
                    // Only what holds of every total order is used, and
                    // comparison is one on every type without floats.
                    "%lessequal" | "%greaterequal" | "%lessthan" | "%greaterthan" => match name {
                        "%lessequal" => self.mk_le(a, b),
                        "%greaterequal" => self.mk_le(b, a),
                        "%lessthan" => {
                            let reverse = self.mk_le(b, a)?;
                            self.mk_not(reverse)
                        }
                        _ => {
                            let reverse = self.mk_le(a, b)?;
                            self.mk_not(reverse)
                        }
                    },
                    _ => unsupported(format!("it uses `{name}`, which the prover does not know")),
                }
            }
            _ => unsupported(format!("it uses `{name}`, which the prover does not know")),
        }
    }

    // --- Proofs -----------------------------------------------------------

    fn enter(&mut self, law: TExprIdx, params: &[Term]) -> Res<(Env, TExprIdx)> {
        let ExpressionDesc::Texp_function {
            params: declared,
            body,
            ..
        } = &self.ta.expr(law).exp_desc
        else {
            return unsupported("it is not a function");
        };
        let mut env = None;
        for (param, term) in self.ta.function_params(*declared).iter().zip(params) {
            env = bind(env, param.fp_param.stamp(), Val::Term(term.clone()));
            env = self.bind_val(env, param.fp_pat, Val::Term(term.clone()))?;
        }
        Ok((env, *body))
    }

    /// The law for these values of its parameters.
    fn goal(&mut self, law: TExprIdx, params: &[Term]) -> Res<Term> {
        let (env, body) = self.enter(law, params)?;
        self.term(body, &env)
    }

    /// The two sides of a law written as `a == b`.
    fn sides(&mut self, law: TExprIdx, params: &[Term]) -> Res<Option<(Term, Term)>> {
        let (env, body) = self.enter(law, params)?;
        let ta = self.ta;
        if let ExpressionDesc::Texp_apply { funct, args, .. } = &ta.expr(body).exp_desc
            && let ExpressionDesc::Texp_ident(_, _, description) = &ta.expr(*funct).exp_desc
            && let ValueKind::ValPrim(primitive) = &description.val_kind
            && primitive.prim_name == "%equal"
            && let [left, right] = ta.apply_args(*args)
            && let (Some(left), Some(right)) = (left.expression, right.expression)
        {
            return Ok(Some((self.term(left, &env)?, self.term(right, &env)?)));
        }
        Ok(None)
    }

    /// The law for these values as a rule, when it has a usable form.
    fn rule(&mut self, law: TExprIdx, params: &[Term], pats: Vec<u32>, kind: Kind) -> Option<Rule> {
        let usable = |lhs: &Term, rhs: &Term| {
            let (mut left, mut right) = (Vec::new(), Vec::new());
            vars(lhs, &mut left);
            vars(rhs, &mut right);
            matches!(lhs, Term::App(..) | Term::Ctor(..) | Term::Prim(..))
                && right
                    .iter()
                    .all(|var| !pats.contains(var) || left.contains(var))
        };
        let (lhs, rhs) = match self.sides(law, params).ok()? {
            Some((left, right)) if left == right => return None,
            Some((left, right)) if usable(&left, &right) => (left, right),
            Some((left, right)) if usable(&right, &left) => (right, left),
            Some(_) => return None,
            None => {
                let whole = self.goal(law, params).ok()?;
                if !usable(&whole, &truth(true)) || is(&whole, true) || is(&whole, false) {
                    return None;
                }
                (whole, truth(true))
            }
        };
        let blank = |term: &Term| {
            pats.iter().fold(term.clone(), |term, pat| {
                subst(&term, *pat, &Term::Var(u32::MAX))
            })
        };
        let ordered = blank(&lhs) == blank(&rhs);
        Some(Rule {
            lhs,
            rhs,
            pats,
            kind,
            ordered,
        })
    }

    /// The constructors of a shape, each with the shapes of its parts.
    fn constructors(&self, shape: &Value) -> Result<Vec<(String, Vec<Value>)>, String> {
        let one = |name: &str, parts: Vec<Value>| (name.to_string(), parts);
        let list = |value: &Value| value.as_array().cloned().unwrap_or_default();
        match shape["k"].as_str().unwrap_or("") {
            "bool" => Ok(vec![one("true", vec![]), one("false", vec![])]),
            "unit" => Ok(vec![one("()", vec![])]),
            "option" => Ok(vec![
                one("None", vec![]),
                one("Some", vec![shape["of"].clone()]),
            ]),
            "list" => Ok(vec![
                one("[]", vec![]),
                one("::", vec![shape["of"].clone(), shape.clone()]),
            ]),
            "tuple" => Ok(vec![one("(,)", list(&shape["of"]))]),
            "named" => {
                let definition = shape["id"].as_str().and_then(|id| self.defs.get(id));
                let Some(definition) = definition else {
                    return Err("it takes apart a value whose type is not known".to_string());
                };
                if definition["k"] == "record" {
                    let fields = list(&definition["fields"]);
                    if fields.iter().any(|field| field["opt"] == true) {
                        return Err("it has a record with optional fields".to_string());
                    }
                    return Ok(vec![one(
                        "{}",
                        fields.iter().map(|field| field["s"].clone()).collect(),
                    )]);
                }
                let mut constructors = Vec::new();
                for case in list(&definition["cases"]) {
                    if case.get("fields").is_some() {
                        return Err("it uses a constructor with an inline record".to_string());
                    }
                    constructors.push(one(
                        case["n"].as_str().unwrap_or(""),
                        case.get("args").map(list).unwrap_or_default(),
                    ));
                }
                Ok(constructors)
            }
            _ => Err("it depends on a value the prover cannot take apart".to_string()),
        }
    }

    /// What a stuck call waits for: the unknown, or the term, that its
    /// function takes apart first.
    fn needed(&mut self, term: &Term) -> Res<Option<Split>> {
        let Term::App(f, args) = term else {
            return Ok(None);
        };
        let Some(FnInfo::Rec(position)) = self.fns.get(f).copied() else {
            return Ok(None);
        };
        match &args[position] {
            Term::Var(var) => Ok(Some(Split::Var(*var))),
            Term::Ctor(..) => match self.unfold(*f, args) {
                Err(Halt::Stuck(Term::Var(var), _)) => Ok(Some(Split::Var(var))),
                Err(Halt::Stuck(inner, shape)) => match self.needed(&inner)? {
                    Some(split) => Ok(Some(split)),
                    None => Ok(Some(Split::Term(inner, shape))),
                },
                Err(halt) => Err(halt),
                Ok(_) => Ok(None),
            },
            inner => self.needed(inner),
        }
    }

    /// What every stuck call of a term waits for.
    fn waiting(&mut self, term: &Term, out: &mut Vec<Split>) -> Res<()> {
        match term {
            Term::Var(_) | Term::Int(_) | Term::Str(_) => {}
            Term::Ctor(_, args) | Term::Prim(_, args) => {
                for arg in args {
                    self.waiting(arg, out)?;
                }
            }
            Term::Sum(terms, _) => {
                for factor in terms.iter().flat_map(|(product, _)| product) {
                    self.waiting(factor, out)?;
                }
            }
            Term::App(_, args) => {
                if let Some(split) = self.needed(term)? {
                    out.push(split);
                }
                for arg in args {
                    self.waiting(arg, out)?;
                }
            }
        }
        Ok(())
    }

    /// What to split on to get a stuck term further: the unknown most of
    /// its calls wait for.
    fn blocker(&mut self, term: &Term) -> Res<Option<Split>> {
        let mut waiting = Vec::new();
        self.waiting(term, &mut waiting)?;
        let unknowns: Vec<u32> = waiting
            .iter()
            .filter_map(|split| match split {
                Split::Var(var) => Some(*var),
                Split::Term(..) => None,
            })
            .collect();
        let count = |var: &u32| unknowns.iter().filter(|other| *other == var).count();
        // The first of the most frequent.
        let best = unknowns.iter().rev().max_by_key(|var| count(var)).copied();
        Ok(match best {
            Some(var) => Some(Split::Var(var)),
            None => waiting.into_iter().next(),
        })
    }

    /// A condition inside a term that is neither true nor false.
    fn condition(term: &Term) -> Option<Term> {
        match term {
            Term::Prim(Op::Not | Op::And | Op::Or, args) => args.iter().find_map(Self::condition),
            Term::Prim(Op::Le | Op::Eq, _) | Term::App(..) => Some(term.clone()),
            _ => None,
        }
    }

    fn search(&mut self, law: TExprIdx, params: &[Term], depth: u32) -> Result<(), String> {
        self.cases += 1;
        if self.cases > CASES || depth > SPLITS {
            return Err("the search for a proof did not end".to_string());
        }
        let split = match self.goal(law, params) {
            Ok(term) if is(&term, true) => {
                self.shown += 1;
                return Ok(());
            }
            Ok(term) if is(&term, false) => {
                return Err("it could not show a case to be true".to_string());
            }
            Ok(term) => match self.blocker(&term) {
                Ok(Some(split)) => split,
                Ok(None) => match Self::condition(&term) {
                    Some(condition) => Split::Term(condition, json!({ "k": "bool" })),
                    None => {
                        return Err(
                            "it comes down to something the prover cannot decide".to_string()
                        );
                    }
                },
                Err(halt) => return Err(describe(halt)),
            },
            Err(Halt::Stuck(term, shape)) => match self.blocker(&term) {
                Ok(Some(split)) => split,
                Ok(None) => Split::Term(term, shape),
                Err(halt) => return Err(describe(halt)),
            },
            Err(halt) => return Err(describe(halt)),
        };
        match split {
            Split::Var(var) | Split::Term(Term::Var(var), _) => {
                self.split_var(law, params, var, depth)
            }
            Split::Term(term, shape) => self.split_term(law, params, term, shape, depth),
        }
    }

    /// One case per constructor of an unknown; by induction when its type
    /// is recursive.
    fn split_var(
        &mut self,
        law: TExprIdx,
        params: &[Term],
        var: u32,
        depth: u32,
    ) -> Result<(), String> {
        let shape = self.var_shapes[var as usize].clone();
        let name = self.var_names[var as usize].clone();
        let constructors = self.constructors(&shape)?;
        let assumed = |rule: &Rc<Rule>| !matches!(rule.kind, Kind::Lemma(_));
        // The law for a part may be used when nothing assumed so far is
        // about this unknown, and for every value of the other unknowns
        // when nothing is assumed at all.
        let inductive = constructors.iter().any(|(_, parts)| parts.contains(&shape))
            && !self
                .rules
                .iter()
                .any(|rule| assumed(rule) && mentions(rule, var));
        let general = !self.rules.iter().any(assumed);
        if inductive && !self.inductions.contains(&name) {
            self.inductions.push(name.clone());
        }
        let saved = self.rules.clone();
        for (constructor, shapes) in constructors {
            self.rules = saved.clone();
            let parts: Vec<Term> = shapes
                .iter()
                .map(|shape| self.fresh(shape.clone(), &name))
                .collect();
            let value = Term::Ctor(constructor, parts.clone());
            if !self.assume(var, &value).map_err(describe)? {
                continue;
            }
            if inductive {
                for (part, part_shape) in parts.iter().zip(&shapes) {
                    if *part_shape != shape {
                        continue;
                    }
                    let smaller: Vec<Term> =
                        params.iter().map(|param| subst(param, var, part)).collect();
                    let mut pats = Vec::new();
                    if general {
                        smaller.iter().for_each(|param| vars(param, &mut pats));
                        pats.retain(|var| Term::Var(*var) != *part);
                    }
                    if let Some(rule) = self.rule(law, &smaller, pats, Kind::Hypothesis) {
                        self.rules.push(Rc::new(rule));
                    }
                }
            }
            let params: Vec<Term> = params
                .iter()
                .map(|param| subst(param, var, &value))
                .collect();
            self.search(law, &params, depth + 1)?;
        }
        self.rules = saved;
        Ok(())
    }

    /// One case per constructor of a term that is not an unknown: each case
    /// assumes the term is that constructor.
    fn split_term(
        &mut self,
        law: TExprIdx,
        params: &[Term],
        term: Term,
        shape: Value,
        depth: u32,
    ) -> Result<(), String> {
        let constructors = self.constructors(&shape)?;
        let name = String::new();
        let saved = self.rules.clone();
        for (constructor, shapes) in constructors {
            self.rules = saved.clone();
            // `x == t` holds: `x` is `t`.
            if constructor == "true"
                && let Term::Prim(Op::Eq, sides) = &term
                && let Some((var, other)) = [(&sides[0], &sides[1]), (&sides[1], &sides[0])]
                    .into_iter()
                    .find_map(|(x, t)| {
                        let mut inside = Vec::new();
                        vars(t, &mut inside);
                        match x {
                            Term::Var(var) if !inside.contains(var) => Some((*var, t.clone())),
                            _ => None,
                        }
                    })
            {
                if self.assume(var, &other).map_err(describe)? {
                    let params: Vec<Term> = params
                        .iter()
                        .map(|param| subst(param, var, &other))
                        .collect();
                    self.search(law, &params, depth + 1)?;
                }
                continue;
            }
            let parts: Vec<Term> = shapes
                .iter()
                .map(|shape| self.fresh(shape.clone(), &name))
                .collect();
            self.rules.push(Rc::new(Rule {
                lhs: term.clone(),
                rhs: Term::Ctor(constructor, parts),
                pats: Vec::new(),
                kind: Kind::Fact,
                ordered: false,
            }));
            self.search(law, params, depth + 1)?;
        }
        self.rules = saved;
        Ok(())
    }

    /// Replaces an unknown by a value in what this case assumes. False
    /// when the assumptions then contradict each other: the case cannot
    /// happen.
    fn assume(&mut self, var: u32, value: &Term) -> Res<bool> {
        let old = std::mem::take(&mut self.rules);
        let (lemmas, others): (Vec<_>, Vec<_>) = old
            .into_iter()
            .partition(|rule| matches!(rule.kind, Kind::Lemma(_)));
        self.rules = lemmas;
        for rule in others {
            if !mentions(&rule, var) {
                self.rules.push(rule);
                continue;
            }
            let (lhs, rhs) = (subst(&rule.lhs, var, value), subst(&rule.rhs, var, value));
            // An assumption that can no longer be stated is dropped: the
            // case then has less to go on, which is safe.
            let (Ok(lhs), Ok(rhs)) = (self.renorm(&lhs), self.renorm(&rhs)) else {
                continue;
            };
            if lhs == rhs {
                continue;
            }
            if rule.kind == Kind::Fact && !matches!(lhs, Term::App(..) | Term::Prim(..)) {
                if let Ok(equal) = self.mk_eq(lhs, rhs)
                    && is(&equal, false)
                {
                    return Ok(false);
                }
                continue;
            }
            self.rules.push(Rc::new(Rule {
                lhs,
                rhs,
                pats: rule.pats.clone(),
                kind: rule.kind.clone(),
                ordered: rule.ordered,
            }));
        }
        Ok(true)
    }
}

fn describe(halt: Halt) -> String {
    match halt {
        Halt::Unsupported(what) => what,
        Halt::Fuel => "the search for a proof did not end".to_string(),
        Halt::Stuck(..) => "it comes down to something the prover cannot decide".to_string(),
    }
}

fn literal(constant: &Constant) -> Res<Term> {
    match constant {
        Constant::Int(n) => Ok(Term::Int(*n as i32)),
        Constant::String(text) => Ok(Term::Str(text.clone())),
        _ => unsupported("it has a number that is not an `int`"),
    }
}

/// Whether a top-level function calls itself, and if so whether every such
/// call passes a part of one of its arguments at that argument's position:
/// then every call ends.
fn structural(ta: &TypedArena, f: i32, params: &[FunctionParam], body: TExprIdx) -> FnInfo {
    let mut walk = Walk {
        ta,
        f,
        origin: HashMap::new(),
        shrinks: vec![true; params.len()],
        calls: 0,
        bad: false,
        unread: false,
    };
    for (position, param) in params.iter().enumerate() {
        walk.origin
            .insert(param.fp_param.stamp(), (position, false));
        walk.bind(param.fp_pat, Some((position, false)), false);
    }
    walk.expr(body);
    if walk.bad {
        FnInfo::Bad
    } else if walk.calls == 0 {
        // Code the prover does not read is reported where it is evaluated.
        FnInfo::Plain
    } else if walk.unread {
        FnInfo::Bad
    } else {
        walk.shrinks
            .iter()
            .position(|shrinks| *shrinks)
            .map_or(FnInfo::Bad, FnInfo::Rec)
    }
}

struct Walk<'a> {
    ta: &'a TypedArena,
    f: i32,
    /// For a name: the parameter it is, or is a part of, and whether it is
    /// a proper part.
    origin: HashMap<i32, (usize, bool)>,
    shrinks: Vec<bool>,
    calls: u32,
    /// The function is used in a way that hides its calls.
    bad: bool,
    /// The function has code the prover does not read.
    unread: bool,
}

impl Walk<'_> {
    fn name(&self, expr: TExprIdx) -> Option<i32> {
        match &self.ta.expr(expr).exp_desc {
            ExpressionDesc::Texp_ident(path, ..) => match path.view() {
                PathView::Pident(id) => Some(id.stamp()),
                _ => None,
            },
            _ => None,
        }
    }

    fn bind(&mut self, pat: TPatIdx, origin: Option<(usize, bool)>, part: bool) {
        let ta = self.ta;
        let name = |this: &mut Self, stamp: i32| {
            if let Some((position, proper)) = origin {
                this.origin.insert(stamp, (position, proper || part));
            }
        };
        match &ta.pattern(pat).pat_desc {
            PatternDesc::Tpat_var(id, _) => name(self, id.stamp()),
            PatternDesc::Tpat_alias(inner, id, _) => {
                name(self, id.stamp());
                self.bind(*inner, origin, part);
            }
            PatternDesc::Tpat_construct(_, _, parts) | PatternDesc::Tpat_tuple(parts) => {
                for inner in ta.pattern_list(*parts) {
                    self.bind(*inner, origin, true);
                }
            }
            PatternDesc::Tpat_record(fields, ..) => {
                for (_, _, inner, _) in fields {
                    self.bind(*inner, origin, true);
                }
            }
            PatternDesc::Tpat_or(left, right, _) => {
                self.bind(*left, origin, part);
                self.bind(*right, origin, part);
            }
            _ => {}
        }
    }

    fn expr(&mut self, idx: TExprIdx) {
        let ta = self.ta;
        match &ta.expr(idx).exp_desc {
            ExpressionDesc::Texp_ident(..) => {
                // The function used as a value: its calls cannot be seen.
                if self.name(idx) == Some(self.f) {
                    self.bad = true;
                }
            }
            ExpressionDesc::Texp_constant(_) => {}
            ExpressionDesc::Texp_apply { funct, args, .. } => {
                let args = ta.apply_args(*args);
                if self.name(*funct) == Some(self.f) {
                    self.calls += 1;
                    if args.len() != self.shrinks.len() {
                        self.bad = true;
                    }
                    for (position, arg) in args.iter().enumerate().take(self.shrinks.len()) {
                        let part = arg
                            .expression
                            .and_then(|expr| self.name(expr))
                            .and_then(|stamp| self.origin.get(&stamp));
                        if part != Some(&(position, true)) {
                            self.shrinks[position] = false;
                        }
                    }
                } else {
                    self.expr(*funct);
                }
                for arg in args {
                    if let Some(expr) = arg.expression {
                        self.expr(expr);
                    }
                }
            }
            ExpressionDesc::Texp_match(scrutinee, cases, exceptions, _) => {
                self.expr(*scrutinee);
                let whole = self
                    .name(*scrutinee)
                    .and_then(|stamp| self.origin.get(&stamp).copied());
                let parts: Vec<Option<(usize, bool)>> = match &ta.expr(*scrutinee).exp_desc {
                    ExpressionDesc::Texp_tuple(items) => ta
                        .expr_list(*items)
                        .iter()
                        .map(|item| {
                            self.name(*item)
                                .and_then(|stamp| self.origin.get(&stamp).copied())
                        })
                        .collect(),
                    _ => Vec::new(),
                };
                for case in ta.cases(*cases) {
                    match &ta.pattern(case.c_lhs).pat_desc {
                        PatternDesc::Tpat_tuple(inner) if !parts.is_empty() => {
                            for (inner, origin) in ta.pattern_list(*inner).iter().zip(&parts) {
                                self.bind(*inner, *origin, false);
                            }
                        }
                        _ => self.bind(case.c_lhs, whole, false),
                    }
                    if let Some(guard) = case.c_guard {
                        self.expr(guard);
                    }
                    self.expr(case.c_rhs);
                }
                for case in ta.cases(*exceptions) {
                    self.expr(case.c_rhs);
                }
            }
            ExpressionDesc::Texp_let(_, bindings, body) => {
                for binding in ta.value_bindings(*bindings) {
                    self.expr(binding.vb_expr);
                }
                self.expr(*body);
            }
            ExpressionDesc::Texp_function { body, .. } => self.expr(*body),
            ExpressionDesc::Texp_tuple(items) | ExpressionDesc::Texp_construct(_, _, items) => {
                for item in ta.expr_list(*items) {
                    self.expr(*item);
                }
            }
            ExpressionDesc::Texp_record {
                fields,
                extended_expression,
                ..
            } => {
                for (_, _, expr) in ta.record_fields(*fields) {
                    self.expr(*expr);
                }
                if let Some(base) = extended_expression {
                    self.expr(*base);
                }
            }
            ExpressionDesc::Texp_field(record, ..) => self.expr(*record),
            ExpressionDesc::Texp_ifthenelse(condition, then, otherwise) => {
                self.expr(*condition);
                self.expr(*then);
                if let Some(otherwise) = otherwise {
                    self.expr(*otherwise);
                }
            }
            ExpressionDesc::Texp_sequence(first, second) => {
                self.expr(*first);
                self.expr(*second);
            }
            // Code the prover does not read: nothing is known about it.
            _ => self.unread = true,
        }
    }
}

/// Tries to prove a law for every value of its parameters. The result is
/// `{"status": "proved", "induction": [names], "lemmas": [names],
/// "cases": n}` or `{"status": "unproved", "reason": text}`.
/// Cost: bounded by a number of evaluation steps; only run by
/// `rescript verify`.
#[allow(clippy::too_many_arguments)]
pub(super) fn prove(
    ctx: &TypeContext,
    ta: &TypedArena,
    index: &Index,
    defs: Definitions,
    law: TExprIdx,
    names: &[String],
    shapes: &[Value],
    lemmas: &[Lemma],
) -> Value {
    let unproved = |reason: String| json!({ "status": "unproved", "reason": reason });
    // `==` is not an equivalence on floats (NaN), and the prover relies on
    // a value being equal to itself.
    let described = format!("{}{}", json!(shapes), defs.to_json());
    if described.contains(r#""k":"float""#) {
        return unproved(
            "it is about floats, where a value need not equal itself (NaN)".to_string(),
        );
    }
    let mut prover = Prover {
        ctx,
        ta,
        index,
        defs,
        fns: HashMap::new(),
        rules: Vec::new(),
        var_shapes: Vec::new(),
        var_names: Vec::new(),
        steps: 0,
        depth: 0,
        cases: 0,
        shown: 0,
        inductions: Vec::new(),
        used: Vec::new(),
    };
    for lemma in lemmas {
        let params: Vec<Term> = lemma
            .shapes
            .iter()
            .map(|shape| prover.fresh(shape.clone(), ""))
            .collect();
        let mut pats = Vec::new();
        params.iter().for_each(|param| vars(param, &mut pats));
        if let Some(rule) = prover.rule(lemma.expr, &params, pats, Kind::Lemma(lemma.name.clone()))
        {
            prover.rules.push(Rc::new(rule));
        }
    }
    prover.steps = 0;
    prover.used.clear();
    let params: Vec<Term> = shapes
        .iter()
        .zip(names)
        .map(|(shape, name)| prover.fresh(shape.clone(), name))
        .collect();
    match prover.search(law, &params, 0) {
        Ok(()) => json!({
            "status": "proved",
            "induction": prover.inductions,
            "lemmas": prover.used,
            "cases": prover.shown,
        }),
        Err(reason) => unproved(reason),
    }
}
