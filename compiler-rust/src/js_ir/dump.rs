//! A compact, one-line textual dump of arena JS IR, for unit tests.
//!
//! Tests assert on the shape of compiled JS IR by comparing a dump against
//! an expected string ([`expect_dump!`](crate::expect_dump)), instead of
//! pattern-matching nested nodes. The dump shows every node kind and payload
//! that changes meaning. Identifiers print by name; within one dump, a second
//! distinct identifier with an already-seen name prints as `name#1` (then
//! `name#2`, ...), so identity relations show without depending on stamps.

use std::fmt::Write;

use ahash::AHashMap;

use super::arena::{Clause, Expr, ExprKind, JsArena, PropName, Stmt, StmtKind, StmtList};
use super::op::{Number, UsedStats};
use super::{CallArity, CallKind};
use crate::ident::Ident;
use crate::lambda::SwitchCaseTag;

/// Dump of one expression.
pub fn expr(a: &JsArena, e: Expr) -> String {
    let mut out = String::new();
    Dumper::new(a, &mut out).expr(e);
    out
}

/// Dump of one statement.
pub fn stmt(a: &JsArena, s: Stmt) -> String {
    let mut out = String::new();
    Dumper::new(a, &mut out).stmt(s);
    out
}

/// Dump of a statement sequence, statements separated by `; `.
pub fn block(a: &JsArena, block: &[Stmt]) -> String {
    let mut out = String::new();
    Dumper::new(a, &mut out).stmts(block);
    out
}

/// Compares `actual` with `expected`. On mismatch it prints an
/// `EXPECT_DUMP` line with the actual dump and panics, unless
/// `EXPECT_DUMP_FILL` is set. `scripts/update_expect_dumps.py [FILTER]` runs
/// the tests that way and rewrites the stale expectations in place.
#[track_caller]
pub fn check(actual: &str, expected: &str, file: &str, line: u32, column: u32) {
    if actual != expected {
        eprintln!(
            "EXPECT_DUMP\t{file}\t{line}\t{column}\t{}",
            serde_json::to_string(actual).expect("a string serializes")
        );
        if std::env::var_os("EXPECT_DUMP_FILL").is_some() {
            return;
        }
        panic!("dump mismatch at {file}:{line}\n  expected: {expected}\n    actual: {actual}");
    }
}

/// `expect_dump!(actual_string, "expected")`: asserts a dump matches.
#[macro_export]
macro_rules! expect_dump {
    ($actual:expr, $expected:expr $(,)?) => {
        $crate::js_ir::dump::check(&$actual, $expected, file!(), line!(), column!())
    };
}

struct Dumper<'a, 'o> {
    a: &'a JsArena,
    out: &'o mut String,
    /// The distinct identifiers seen so far for each name, in order.
    seen: AHashMap<&'static str, Vec<Ident>>,
}

impl<'a, 'o> Dumper<'a, 'o> {
    fn new(a: &'a JsArena, out: &'o mut String) -> Self {
        Dumper {
            a,
            out,
            seen: AHashMap::new(),
        }
    }

    /// The printed form of `id`: its name, plus `#k` for the k-th distinct
    /// identifier with that name (k > 0).
    fn ident(&mut self, id: Ident) -> String {
        let name = id.name();
        let seen = self.seen.entry(name).or_default();
        let k = match seen.iter().position(|other| other.same(&id)) {
            Some(k) => k,
            None => {
                seen.push(id);
                seen.len() - 1
            }
        };
        if k == 0 {
            name.to_string()
        } else {
            format!("{name}#{k}")
        }
    }
}

impl Dumper<'_, '_> {
    fn w(&mut self, s: &str) {
        self.out.push_str(s);
    }

    fn list(&mut self, items: &[Expr]) {
        for (i, e) in items.iter().enumerate() {
            if i > 0 {
                self.w(", ");
            }
            self.expr(*e);
        }
    }

    fn comment(&mut self, c: Option<&str>) {
        if let Some(c) = c {
            let _ = write!(self.out, "/*{c}*/ ");
        }
    }

    fn label(&mut self, l: Option<super::arena::StrId>) {
        if let Some(l) = l {
            let _ = write!(self.out, "[{}]", self.a.text(l));
        }
    }

    fn expr(&mut self, e: Expr) {
        let a = self.a;
        self.comment(a.expr_comment(e));
        match a.ek(e) {
            ExprKind::Length(x, obj) => {
                let _ = write!(self.out, "Length[{obj:?}](");
                self.expr(x);
                self.w(")");
            }
            ExprKind::IsNullOrUndefined(x) => self.unary("IsNullOrUndefined", x),
            ExprKind::Typeof(x) => self.unary("Typeof", x),
            ExprKind::JsNot(x) => self.unary("Not", x),
            ExprKind::JsBnot(x) => self.unary("Bnot", x),
            ExprKind::Await(x) => self.unary("Await", x),
            ExprKind::Spread(x) => self.unary("Spread", x),
            ExprKind::StringAppend(l, r) => self.binary("StringAppend", l, r),
            ExprKind::In(l, r) => self.binary("In", l, r),
            ExprKind::Seq(l, r) => self.binary("Seq", l, r),
            ExprKind::FlatCall(l, r) => self.binary("FlatCall", l, r),
            ExprKind::ArrayIndex(l, r) => self.binary("ArrayIndex", l, r),
            ExprKind::Bin(op, l, r) => self.binary(&format!("{op:?}"), l, r),
            ExprKind::Bool(b) => {
                let _ = write!(self.out, "{b}");
            }
            ExprKind::Cond(c, t, f) => {
                self.w("Cond(");
                self.list(&[c, t, f]);
                self.w(")");
            }
            ExprKind::Call(f, args, info) => {
                let info = a.call_info(info);
                self.w("Call");
                let mut flags = Vec::new();
                if info.is_method {
                    flags.push("method".to_string());
                }
                if info.call_transformed_jsx {
                    flags.push("jsx".to_string());
                }
                match info.kind {
                    CallKind::MlCall => {}
                    kind => flags.push(format!("{kind:?}")),
                }
                if matches!(info.arity, CallArity::Full) {
                    flags.push("full".to_string());
                }
                if let Some(c) = &info.comment {
                    flags.push(format!("/*{c}*/"));
                }
                if !flags.is_empty() {
                    let _ = write!(self.out, "[{}]", flags.join(","));
                }
                self.w("(");
                self.expr(f);
                self.w("; ");
                self.list(a.exprs(args));
                self.w(")");
            }
            ExprKind::TaggedTemplate(tag, strings, values) => {
                let _ = write!(self.out, "TaggedTemplate({:?}, ", a.tagged(strings));
                self.expr(tag);
                self.w("; ");
                self.list(a.exprs(values));
                self.w(")");
            }
            ExprKind::InterpolatedTemplate(segments, values) => {
                let _ = write!(self.out, "Template({:?}; ", a.segments(segments));
                self.list(a.exprs(values));
                self.w(")");
            }
            ExprKind::StaticIndex(x, field, pos) => {
                self.expr(x);
                let _ = write!(self.out, ".{}", a.text(field));
                if let Some(pos) = pos.get() {
                    let _ = write!(self.out, "@{pos}");
                }
            }
            ExprKind::New(f, args) => {
                self.w("New(");
                self.expr(f);
                if let Some(args) = args {
                    self.w("; ");
                    self.list(a.exprs(args));
                }
                self.w(")");
            }
            ExprKind::Var(id) => {
                let name = self.ident(a.ident(id));
                self.w(&name);
            }
            ExprKind::Qualified(q) => {
                let (module, member) = a.qual(q);
                let _ = write!(self.out, "{}", module.id.name());
                if let Some(member) = member {
                    let _ = write!(self.out, ".{member}");
                }
                let _ = write!(self.out, "<{:?}", module.kind);
                if module.dynamic_import {
                    self.w(",dynamic");
                }
                self.w(">");
            }
            ExprKind::Fun(f) => {
                let info = a.fun(f);
                self.w("Fun");
                let mut flags = Vec::new();
                if info.is_method {
                    flags.push("method");
                }
                if info.async_ {
                    flags.push("async");
                }
                if info.return_unit {
                    flags.push("unit");
                }
                if !flags.is_empty() {
                    let _ = write!(self.out, "[{}]", flags.join(","));
                }
                self.w("(");
                let names: Vec<String> = a
                    .ident_slice(info.params)
                    .iter()
                    .map(|p| self.ident(*p))
                    .collect();
                self.w(&names.join(", "));
                self.w(")");
                if let Some(d) = info.directive {
                    let _ = write!(self.out, "\"{}\"", a.text(d));
                }
                self.braced(info.body);
            }
            ExprKind::Str(s) => {
                let _ = write!(self.out, "{:?}", a.text(s));
            }
            ExprKind::TemplateLiteral(t) => {
                let _ = write!(self.out, "TemplateLiteral({:?})", a.template(t));
            }
            ExprKind::JsonLiteral(s) => {
                let _ = write!(self.out, "Json({:?})", a.text(s));
            }
            ExprKind::RawJsCode(r) => {
                let r = a.raw(r);
                let _ = write!(
                    self.out,
                    "Raw{}({:?})",
                    if r.is_stmt { "Stmt" } else { "" },
                    r.code
                );
            }
            ExprKind::Array(items, flag) => {
                let _ = write!(self.out, "Array[{flag:?}](");
                self.list(a.exprs(items));
                self.w(")");
            }
            ExprKind::OptionalBlock(x, identity) => {
                let _ = write!(self.out, "OptionalBlock[{identity}](");
                self.expr(x);
                self.w(")");
            }
            ExprKind::CamlBlock(items, flag, tag) => {
                let _ = write!(self.out, "CamlBlock[{flag:?}, {:?}](", a.tag(tag));
                self.list(a.exprs(items));
                self.w(")");
            }
            ExprKind::CamlBlockTag(x, name) => {
                let _ = write!(self.out, "CamlBlockTag[{}](", a.text(name));
                self.expr(x);
                self.w(")");
            }
            ExprKind::Number(n) => match a.number(n) {
                Number::Int { i, c: None } => {
                    let _ = write!(self.out, "{i}");
                }
                n => {
                    let _ = write!(self.out, "{n:?}");
                }
            },
            ExprKind::Object(props) => {
                self.w("{");
                for (i, (name, value)) in a.props(props).iter().enumerate() {
                    if i > 0 {
                        self.w(", ");
                    }
                    match name {
                        PropName::Lit(s) => {
                            let _ = write!(self.out, "{:?}: ", a.text(*s));
                        }
                        PropName::Symbol => self.w("[symbol]: "),
                        PropName::Spread => self.w("..."),
                        PropName::RecordSpread => self.w("...record "),
                    }
                    self.expr(*value);
                }
                self.w("}");
            }
            ExprKind::Undefined { is_unit } => self.w(if is_unit { "unit" } else { "undefined" }),
            ExprKind::Null => self.w("null"),
            ExprKind::Jsx(id) => {
                let jsx = a.jsx(id);
                self.w("Jsx(");
                for (i, value) in jsx.expressions(a).enumerate() {
                    if i > 0 {
                        self.w(", ");
                    }
                    self.expr(value);
                }
                self.w(")");
            }
            ExprKind::RecordRest(fields, source) => {
                let fields: Vec<String> = a
                    .rest(fields)
                    .iter()
                    .map(|f| match f.ident {
                        Some(id) => format!("{}: {}", f.label, self.ident(id)),
                        None => format!("...{}", f.label),
                    })
                    .collect();
                let _ = write!(self.out, "RecordRest({}; ", fields.join(", "));
                self.expr(source);
                self.w(")");
            }
        }
        if let Some(loc) = a.expr_loc(e) {
            let _ = write!(self.out, "@{loc:?}");
        }
    }

    fn unary(&mut self, name: &str, x: Expr) {
        self.w(name);
        self.w("(");
        self.expr(x);
        self.w(")");
    }

    fn binary(&mut self, name: &str, l: Expr, r: Expr) {
        self.w(name);
        self.w("(");
        self.expr(l);
        self.w(", ");
        self.expr(r);
        self.w(")");
    }

    fn stmts(&mut self, block: &[Stmt]) {
        for (i, s) in block.iter().enumerate() {
            if i > 0 {
                self.w("; ");
            }
            self.stmt(*s);
        }
    }

    fn braced(&mut self, block: StmtList) {
        self.w("{");
        self.stmts(self.a.stmts(block));
        self.w("}");
    }

    fn clause(&mut self, clause: &Clause) {
        let a = self.a;
        self.comment(clause.comment.map(|c| a.text(c)));
        self.braced(clause.body);
        if clause.should_break {
            self.w(" break");
        }
    }

    fn stmt(&mut self, s: Stmt) {
        let a = self.a;
        self.comment(a.stmt_comment(s));
        match a.sk(s) {
            StmtKind::Block(b) => {
                self.w("Block");
                self.braced(b);
            }
            StmtKind::Variable(v) => {
                let decl = a.var(v);
                let _ = write!(self.out, "let[{:?}", decl.property);
                if decl.ident_info.used_stats != UsedStats::default() {
                    let _ = write!(self.out, ",{:?}", decl.ident_info.used_stats);
                }
                let name = self.ident(decl.ident);
                let _ = write!(self.out, "] {name}");
                if let Some(value) = decl.value {
                    self.w(" = ");
                    self.expr(value);
                }
            }
            StmtKind::Exp(e) => {
                self.w("Exp(");
                self.expr(e);
                self.w(")");
            }
            StmtKind::Return(e) => {
                self.w("Return(");
                self.expr(e);
                self.w(")");
            }
            StmtKind::Throw(e) => {
                self.w("Throw(");
                self.expr(e);
                self.w(")");
            }
            StmtKind::If(c, t, f) => {
                self.w("If(");
                self.expr(c);
                self.w(") ");
                self.braced(t);
                self.w(" else ");
                self.braced(f);
            }
            StmtKind::While(label, c, body) => {
                self.w("While");
                self.label(label);
                self.w("(");
                self.expr(c);
                self.w(") ");
                self.braced(body);
            }
            StmtKind::ForRange(info) => {
                let info = a.for_range(info);
                self.w("For");
                self.label(info.label);
                let name = self.ident(a.ident(info.ident));
                let _ = write!(self.out, "({name} = ");
                match info.init {
                    Some(init) => self.expr(init),
                    None => self.w("_"),
                }
                let _ = write!(self.out, "; {:?} ", info.direction);
                self.expr(info.end);
                self.w(") ");
                self.braced(info.body);
            }
            StmtKind::ForOf(info) | StmtKind::ForAwaitOf(info) => {
                let await_ = matches!(a.sk(s), StmtKind::ForAwaitOf(_));
                let info = a.for_of(info);
                self.w(if await_ { "ForAwaitOf" } else { "ForOf" });
                self.label(info.label);
                let name = self.ident(a.ident(info.ident));
                let _ = write!(self.out, "({name} of ");
                self.expr(info.iterable);
                self.w(") ");
                self.braced(info.body);
            }
            StmtKind::Continue(label) => {
                self.w("Continue");
                self.label(label);
            }
            StmtKind::Break(label) => {
                self.w("Break");
                self.label(label);
            }
            StmtKind::IntSwitch(test, info) => {
                let info = a.int_switch(info);
                self.w("Switch(");
                self.expr(test);
                self.w(") {");
                for (case, clause) in &info.clauses {
                    let _ = write!(self.out, "case {case}: ");
                    self.clause(clause);
                    self.w(" ");
                }
                if let Some(default) = info.default {
                    self.w("default: ");
                    self.braced(default);
                }
                self.w("}");
            }
            StmtKind::StringSwitch(test, info) => {
                let info = a.string_switch(info);
                self.w("StringSwitch(");
                self.expr(test);
                self.w(") {");
                for clause in &info.clauses {
                    match &clause.tag_type {
                        SwitchCaseTag::String(s) => {
                            let _ = write!(self.out, "case {s:?}: ");
                        }
                        tag => {
                            let _ = write!(self.out, "case {tag:?}: ");
                        }
                    }
                    self.clause(&clause.clause);
                    self.w(" ");
                }
                if let Some(default) = info.default {
                    self.w("default: ");
                    self.braced(default);
                }
                self.w("}");
            }
            StmtKind::Try(info) => {
                let info = a.try_info(info);
                self.w("Try");
                self.braced(info.body);
                if let Some((id, body)) = info.catch {
                    let name = self.ident(a.ident(id));
                    let _ = write!(self.out, " catch({name})");
                    self.braced(body);
                }
                if let Some(finally) = info.finally {
                    self.w(" finally");
                    self.braced(finally);
                }
            }
            StmtKind::Debugger => self.w("Debugger"),
        }
        if let Some(loc) = a.stmt_loc(s) {
            let _ = write!(self.out, "@{loc:?}");
        }
    }
}
