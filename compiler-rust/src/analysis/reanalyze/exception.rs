//! The exception analysis: which exceptions each value may throw, against
//! its `@throws` annotation (`Exception`, `Exn`, `Exceptions` and
//! `Module_path`'s aliases in analysis/reanalyze/src).
//!
//! Each implementation yields the annotations of its values and, per value,
//! the events of its body: throws, calls, catches. Once every file is read,
//! a value's events are combined into the set it throws, looking calls up in
//! the annotations of all files and in the table of library functions
//! (`exn_lib`).

use super::annotation::{self, AttributePayload};
use super::common::*;
use super::exn_lib;
use super::log::{Description, Exceptions, LocKey, Log, MissingThrowInfo, pp_exceptions};
use super::traverse::{self, Visitor};
use crate::parser::ast::Attributes;
use crate::types::typedtree as tt;
use crate::types::typedtree::{TExprIdx, TModExprIdx};
use std::collections::{BTreeMap, BTreeSet, HashMap};

/// `Exn.match_failure`.
const MATCH_FAILURE: &str = "Match_failure";

/// `Exception.Event.kind`.
#[derive(Debug, Clone)]
enum EventKind {
    /// `try ... catch { | E => ... }`: the events of the body.
    Catches(Events),
    /// A use of a value.
    Call {
        /// The value's path.
        callee: DcePath,
        /// The modules the use is in.
        module_path: DcePath,
    },
    /// An expression annotated `@doesNotThrow`: its events.
    DoesNotThrow(Events),
    /// `throw(E)`.
    Throws,
}

/// `Exception.Event.t`.
#[derive(Debug, Clone)]
struct Event {
    exceptions: Exceptions,
    kind: EventKind,
    loc: Loc,
}

/// Events in the order they happen. OCaml conses each onto a list, so it
/// reads them latest first; so do the readers here.
type Events = Vec<Event>;

/// `Exception.check`: a value's events and the exceptions it is annotated
/// with.
#[derive(Debug)]
struct Check {
    events: Events,
    loc: Loc,
    loc_full: Loc,
    module_name: String,
    exn_name: String,
    exceptions: Exceptions,
}

/// `Exception.file_result`: what one implementation contributes.
#[derive(Debug)]
pub struct FileResult {
    /// The file's module.
    pub module_name: String,
    /// The exceptions each value is annotated with, by the value's dotted
    /// path within the file.
    values: HashMap<String, Exceptions>,
    checks: Vec<Check>,
}

/// `Exception.values_table`: every file's annotations, by module name.
type ValuesTable<'a> = HashMap<&'a str, &'a HashMap<String, Exceptions>>;

/// `String.capitalize_ascii` and `String.uncapitalize_ascii`.
fn with_first_char(s: &str, f: impl Fn(&u8) -> u8) -> String {
    let mut bytes = s.as_bytes().to_vec();
    if let Some(first) = bytes.first_mut() {
        *first = f(first);
    }
    String::from_utf8(bytes).unwrap_or_else(|_| s.to_string())
}

/// `path @ module_path |> Dce_path.to_name`.
fn name_in(path: &[Name], module_path: &[Name]) -> String {
    let mut full: DcePath = path.to_vec();
    full.extend(module_path.iter().cloned());
    path_to_string(&full)
}

/// `Exception.Values.get_from_module`.
fn get_from_module<'a>(
    table: &ValuesTable<'a>,
    module_name: &str,
    module_path: &[Name],
    path: &[Name],
) -> Option<&'a Exceptions> {
    let name = name_in(path, module_path);
    let capitalized = with_first_char(module_name, u8::to_ascii_uppercase);
    match table.get(capitalized.as_str()) {
        Some(values) => values.get(&name),
        None => table
            .get(with_first_char(module_name, u8::to_ascii_lowercase).as_str())
            .and_then(|values| values.get(&name)),
    }
}

/// `Exception.Values.find_path`: the annotation of the value a call names,
/// in the modules enclosing the call, innermost first, then in another file.
fn find_path<'a>(
    table: &ValuesTable<'a>,
    module_name: &str,
    module_path: &[Name],
    path: &[Name],
) -> Option<&'a Exceptions> {
    let mut enclosing = module_path;
    loop {
        if let Some(found) = get_from_module(table, module_name, enclosing, path) {
            return Some(found);
        }
        match enclosing {
            [] => break,
            [_, rest @ ..] => enclosing = rest,
        }
    }
    // The outermost name is another file's module.
    let (external_module_name, rest) = path.split_last()?;
    get_from_module(table, external_module_name, &[], rest)
}

/// `Exceptions.pp ~exn_table:None` on the standard formatter, where names
/// are tagged.
fn pp_tagged(log: &Log<'_>, exceptions: &Exceptions) -> String {
    let mut out = String::new();
    let is_list = exceptions.len() > 1;
    if is_list {
        out.push('[');
    }
    for (i, name) in exceptions.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        out.push_str(&log.tag("info", name));
    }
    if is_list {
        out.push(']');
    }
    out
}

/// `Exception.Event.print`: the event and a line end.
fn print_event(log: &Log<'_>, event: &Event) -> String {
    let pos = log.pos_string(&event.loc.start);
    let nested = |events: &Events| -> String {
        events
            .iter()
            .rev()
            .map(|event| format!("{} ", print_event(log, event)))
            .collect()
    };
    match &event.kind {
        EventKind::Call {
            callee,
            module_path,
        } => format!(
            "{pos} Call({}, module_path:{}) {}\n",
            path_to_string(callee),
            path_to_string(module_path),
            pp_tagged(log, &event.exceptions)
        ),
        EventKind::DoesNotThrow(events) => {
            format!("{pos} DoesNotThrow({})\n", nested(events))
        }
        EventKind::Throws => format!("{pos} throws {}\n", pp_tagged(log, &event.exceptions)),
        EventKind::Catches(events) => format!(
            "{pos} Catches exceptions:{} nested_events:{}\n",
            pp_tagged(log, &event.exceptions),
            nested(events)
        ),
    }
}

/// Where each exception of a value is thrown (`exn_table`).
type ExnTable = BTreeMap<String, BTreeSet<LocKey>>;

/// `Exception.Event.combine`'s state.
struct Combine<'a, 'l, 'c> {
    table: &'a ValuesTable<'a>,
    log: &'l mut Log<'c>,
    files: &'a Files,
    debug: bool,
    module_name: &'a str,
    exn_table: ExnTable,
}

impl Combine<'_, '_, '_> {
    fn extend_exn_table(&mut self, exceptions: &Exceptions, loc: &Loc) {
        for exn in exceptions {
            self.exn_table
                .entry(exn.clone())
                .or_default()
                .insert(LocKey::new(self.files, loc));
        }
    }

    /// The exceptions `events` throw, added to `exn_set`.
    fn combine(&mut self, mut exn_set: Exceptions, events: &Events) -> Exceptions {
        for event in events.iter().rev() {
            if self.debug {
                let text = print_event(self.log, event);
                self.log.item(&format!("{text}\n"));
            }
            match &event.kind {
                EventKind::Throws => {
                    self.extend_exn_table(&event.exceptions, &event.loc);
                    exn_set.extend(event.exceptions.iter().cloned());
                }
                EventKind::Call {
                    callee,
                    module_path,
                } => {
                    let exceptions = find_path(self.table, self.module_name, module_path, callee)
                        .cloned()
                        .or_else(|| exn_lib::find(&path_to_string(callee)))
                        .unwrap_or_default();
                    self.extend_exn_table(&exceptions, &event.loc);
                    exn_set.extend(exceptions);
                }
                EventKind::DoesNotThrow(nested_events) => {
                    let nested_exceptions = self.combine(Exceptions::new(), nested_events);
                    if nested_exceptions.is_empty() {
                        let name = match nested_events.last() {
                            Some(Event {
                                kind: EventKind::Call { callee, .. },
                                ..
                            }) => path_to_string(callee),
                            _ => "expression".to_string(),
                        };
                        self.log.warning(
                            event.loc,
                            Description::ExceptionAnalysis {
                                message: format!(
                                    "{name} does not throw and is annotated with redundant @doesNotThrow"
                                ),
                            },
                        );
                    }
                }
                EventKind::Catches(nested_events) => {
                    // No exceptions is a catch-all.
                    if !event.exceptions.is_empty() {
                        let nested_exceptions = self.combine(Exceptions::new(), nested_events);
                        for exn in &event.exceptions {
                            if let Some(locs) = self.exn_table.get_mut(exn) {
                                for nested in nested_events {
                                    locs.remove(&LocKey::new(self.files, &nested.loc));
                                }
                            }
                        }
                        exn_set.extend(
                            nested_exceptions
                                .into_iter()
                                .filter(|exn| !event.exceptions.contains(exn)),
                        );
                    }
                }
            }
        }
        exn_set
    }
}

/// `Exception.Checks.do_check`.
fn do_check(
    table: &ValuesTable<'_>,
    config: &Config,
    files: &Files,
    log: &mut Log<'_>,
    check: &Check,
) {
    let debug = config.cli.debug;
    if debug {
        log.item("\n");
        log.item(&format!("Events combine: #events {}\n", check.events.len()));
    }
    let mut combine = Combine {
        table,
        log,
        files,
        debug,
        module_name: &check.module_name,
        exn_table: ExnTable::new(),
    };
    let throw_set = combine.combine(Exceptions::new(), &check.events);
    let exn_table = combine.exn_table;
    let missing_annotations: Exceptions =
        throw_set.difference(&check.exceptions).cloned().collect();
    let redundant_annotations: Exceptions =
        check.exceptions.difference(&throw_set).cloned().collect();
    let redundant = (!redundant_annotations.is_empty()).then(|| {
        let throws_description = if throw_set.is_empty() {
            "throws nothing".to_string()
        } else {
            format!(
                "might throw {}",
                pp_exceptions(Some(&exn_table), &throw_set)
            )
        };
        format!(
            "{} {throws_description} and is annotated with redundant @throws({})",
            check.exn_name,
            pp_exceptions(None, &redundant_annotations)
        )
    });
    if !missing_annotations.is_empty() {
        log.warning(
            check.loc,
            Description::ExceptionAnalysisMissing(MissingThrowInfo {
                exn_name: check.exn_name.clone(),
                exn_table,
                loc_full: check.loc_full,
                missing_annotations,
                throw_set,
            }),
        );
    }
    if let Some(message) = redundant {
        log.warning(check.loc, Description::ExceptionAnalysis { message });
    }
}

/// `Exception.run_checks`: report every value of `results` whose
/// annotation and thrown exceptions differ.
pub fn run_checks(config: &Config, files: &Files, log: &mut Log<'_>, mut results: Vec<FileResult>) {
    // The order of the checks must not depend on the order of the files.
    results.sort_by(|a, b| a.module_name.cmp(&b.module_name));
    let table: ValuesTable<'_> = results
        .iter()
        .map(|result| (result.module_name.as_str(), &result.values))
        .collect();
    for result in &results {
        for check in &result.checks {
            do_check(&table, config, files, log, check);
        }
    }
}

/// `Module_path.normalize_path`: `path` with its outermost module replaced
/// by the path it is an alias of.
fn normalize_path(
    aliases: &BTreeMap<Name, DcePath>,
    path: DcePath,
    log: Option<&mut Log<'_>>,
) -> DcePath {
    let [rest @ .., name] = path.as_slice() else {
        return path;
    };
    if rest.is_empty() {
        return path;
    }
    let Some(alias) = aliases.get(name) else {
        return path;
    };
    // `List.rev (path1 @ rest_rev)`, with `rest_rev` the outermost-first
    // rest of the path.
    let mut new_path: DcePath = rest.to_vec();
    new_path.extend(alias.iter().rev().cloned());
    if let Some(log) = log {
        log.item(&format!(
            "Resolve Alias: {} to {}\n",
            path_to_string(&path),
            path_to_string(&new_path)
        ));
    }
    new_path
}

fn is_throw(name: &str) -> bool {
    name == "Pervasives.raise" || name == "Pervasives.throw"
}

/// `/` and `mod` are listed in `exn_lib` as throwing `Division_by_zero`.
/// They cannot throw when the divisor is a non-zero literal, as in `x / 10`.
fn is_division(name: &str) -> bool {
    matches!(
        name,
        "Pervasives./" | "Pervasives.mod" | "Stdlib./" | "Stdlib.mod"
    )
}

/// `float_of_string_opt`, for the decimal and hexadecimal literals the
/// parser accepts.
fn float_of_string(s: &str) -> Option<f64> {
    let digits: String = s.chars().filter(|c| *c != '_').collect();
    if let Ok(value) = digits.parse::<f64>() {
        return Some(value);
    }
    let (negative, unsigned) = match digits.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, digits.as_str()),
    };
    let hex = unsigned
        .strip_prefix("0x")
        .or_else(|| unsigned.strip_prefix("0X"))?;
    let (mantissa, exponent) = match hex.find(['p', 'P']) {
        Some(i) => (&hex[..i], hex[i + 1..].parse::<i32>().ok()?),
        None => (hex, 0),
    };
    let (int_part, frac_part) = mantissa.split_once('.').unwrap_or((mantissa, ""));
    let mut value = 0f64;
    for c in int_part.chars() {
        value = value * 16.0 + f64::from(c.to_digit(16)?);
    }
    let mut scale = 1.0 / 16.0;
    for c in frac_part.chars() {
        value += f64::from(c.to_digit(16)?) * scale;
        scale /= 16.0;
    }
    let value = value * 2f64.powi(exponent);
    Some(if negative { -value } else { value })
}

fn is_non_zero_constant(constant: &tt::Constant) -> bool {
    match constant {
        tt::Constant::Int(n) => *n != 0,
        tt::Constant::Float(s) => float_of_string(s).is_some_and(|f| f != 0.0),
        tt::Constant::BigInt(_, digits) => digits.chars().any(|c| ('1'..='9').contains(&c)),
        tt::Constant::Char(_) | tt::Constant::String(_) => false,
    }
}

/// The `@doesNotThrow` annotation, in every spelling the OCaml tool reads.
fn is_does_not_throw_name(name: &str) -> bool {
    matches!(
        name,
        "doesNotRaise"
            | "doesnotraise"
            | "DoesNoRaise"
            | "doesNotraise"
            | "doNotRaise"
            | "donotraise"
            | "DoNoRaise"
            | "doNotraise"
            | "doesNotThrow"
            | "doesnotthrow"
            | "DoesNoThrow"
            | "doesNotthrow"
            | "doNotThrow"
            | "donotthrow"
            | "DoNoThrow"
            | "doNotthrow"
    )
}

/// The exceptions an annotation's payload names.
fn exceptions_of_payload(payload: &AttributePayload, exceptions: &mut Exceptions) {
    match payload {
        AttributePayload::String(s) | AttributePayload::Ident(s) => {
            exceptions.insert(s.clone());
        }
        AttributePayload::Construct(s) if s != "::" => {
            exceptions.insert(s.clone());
        }
        AttributePayload::Tuple(payloads) => {
            for payload in payloads {
                exceptions_of_payload(payload, exceptions);
            }
        }
        _ => {}
    }
}

/// `Exception.traverse_ast`'s state.
struct Traverse<'t, 'l, 'c> {
    tree: &'t Tree<'t>,
    log: &'l mut Log<'c>,
    debug: bool,
    module_name: &'t str,
    module_path: ModulePath,
    /// The value whose events are collected: none at the top level.
    current_id: Option<String>,
    current_events: Events,
    values: HashMap<String, Exceptions>,
    checks: Vec<Check>,
}

impl<'t> Traverse<'t, '_, '_> {
    fn push(&mut self, exceptions: Exceptions, loc: Loc, kind: EventKind) {
        self.current_events.push(Event {
            exceptions,
            kind,
            loc,
        });
    }

    fn does_not_throw(&self, attributes: &Attributes) -> bool {
        annotation::has_attribute(self.tree.arena, is_does_not_throw_name, attributes.iter())
    }

    /// `get_exceptions_from_annotations`.
    fn exceptions_from_annotations(&self, attributes: &Attributes) -> Exceptions {
        let mut exceptions = Exceptions::new();
        let payload = annotation::get_attribute_payload(
            self.tree.arena,
            |s| matches!(s, "throws" | "throw" | "raises" | "raise"),
            attributes.iter(),
        );
        if let Some(payload) = payload {
            exceptions_of_payload(&payload, &mut exceptions);
        }
        exceptions
    }

    /// `throw_args`: the exception a `throw` is applied to.
    fn throw_args(&self, args: &[tt::ApplyArg]) -> Exceptions {
        let name = match args {
            [
                tt::ApplyArg {
                    expression: Some(arg),
                    ..
                },
            ] => match &self.tree.ta.expr(*arg).exp_desc {
                tt::ExpressionDesc::Texp_construct(lid, _, _) => self.tree.lid_string(lid.txt),
                tt::ExpressionDesc::Texp_ident(..) => "genericException".to_string(),
                _ => "TODO_from_raise1".to_string(),
            },
            _ => "TODO_from_raise1".to_string(),
        };
        Exceptions::from([name])
    }

    fn divides_by_non_zero_constant(&self, args: &[tt::ApplyArg]) -> bool {
        match args {
            [
                _,
                tt::ApplyArg {
                    expression: Some(divisor),
                    ..
                },
            ] => match &self.tree.ta.expr(*divisor).exp_desc {
                tt::ExpressionDesc::Texp_constant(constant) => is_non_zero_constant(constant),
                _ => false,
            },
            _ => false,
        }
    }

    /// The application of the value named `callee_name`.
    fn apply(&mut self, callee_name: &str, funct: TExprIdx, args: &'t [tt::ApplyArg], loc: Loc) {
        let ta = self.tree.ta;
        // `throw @@ Exn(...)`.
        let applied_throw = match args {
            [first, arg] if callee_name == "Pervasives.@@" => first
                .expression
                .is_some_and(|first| match &ta.expr(first).exp_desc {
                    tt::ExpressionDesc::Texp_ident(thrower, _, _) => is_throw(&thrower.name()),
                    _ => false,
                })
                .then_some(arg),
            _ => None,
        };
        if let Some(arg) = applied_throw {
            let exceptions = self.throw_args(std::slice::from_ref(arg));
            self.push(exceptions, loc, EventKind::Throws);
            self.expr_opt(arg.expression);
            return;
        }
        if is_throw(callee_name) {
            let exceptions = self.throw_args(args);
            self.push(exceptions, loc, EventKind::Throws);
        } else if !(is_division(callee_name) && self.divides_by_non_zero_constant(args)) {
            self.expr(funct);
        }
        for arg in args {
            self.expr_opt(arg.expression);
        }
    }

    fn expr_opt(&mut self, e: Option<TExprIdx>) {
        if let Some(e) = e {
            self.expr(e);
        }
    }

    /// `iter_cases`. Patterns hold no expressions.
    fn cases(&mut self, cases: &'t [tt::Case]) {
        for case in cases {
            self.expr_opt(case.c_guard);
            self.expr(case.c_rhs);
        }
    }

    /// `exceptions_of_patterns`: the exceptions the patterns of `cases`
    /// name.
    fn exceptions_of_cases(&self, cases: &[tt::Case]) -> Exceptions {
        cases
            .iter()
            .filter_map(|case| match &self.tree.ta.pattern(case.c_lhs).pat_desc {
                tt::PatternDesc::Tpat_construct(lid, _, _) => Some(self.tree.lid_string(lid.txt)),
                _ => None,
            })
            .collect()
    }

    /// Visit `body` collecting its events apart, and record that
    /// `exceptions` of them are caught.
    fn catches(&mut self, body: TExprIdx, exceptions: Exceptions, loc: Loc) {
        let old_events = std::mem::take(&mut self.current_events);
        self.expr(body);
        let nested = std::mem::replace(&mut self.current_events, old_events);
        self.push(exceptions, loc, EventKind::Catches(nested));
    }

    /// `Module_path.resolve_alias`.
    fn resolve_alias(&mut self, path: DcePath) -> DcePath {
        let log = self.debug.then_some(&mut *self.log);
        normalize_path(&self.module_path.aliases, path, log)
    }

    /// `Module_path.add_alias` to the current module path.
    fn add_alias(&mut self, name: Name, path: DcePath) {
        let log = self.debug.then_some(&mut *self.log);
        let normalized = normalize_path(&self.module_path.aliases, path, log);
        if self.debug {
            self.log.item(&format!(
                "Module Alias: {name} = {}\n",
                path_to_string(&normalized)
            ));
        }
        self.module_path.aliases.insert(name, normalized);
    }

    /// `find_local_path`: the annotation of the value `name` in the modules
    /// enclosing it in this file, innermost first.
    fn find_local_path(&self, name: &Name) -> Option<&Exceptions> {
        let path = std::slice::from_ref(name);
        let mut enclosing = self.module_path.path.as_slice();
        loop {
            if let Some(found) = self.values.get(&name_in(path, enclosing)) {
                return Some(found);
            }
            match enclosing {
                [] => return None,
                [_, rest @ ..] => enclosing = rest,
            }
        }
    }

    /// `process_binding`: the events of the binding of `name` are its own.
    fn process_binding(&mut self, name: &str, vb: &'t tt::ValueBinding) {
        let old_id = self.current_id.replace(name.to_string());
        let old_events = std::mem::take(&mut self.current_events);
        let annotated = self.exceptions_from_annotations(&vb.vb_attributes);
        let name_in_path = name_create(name, true);
        self.values.insert(
            name_in(std::slice::from_ref(&name_in_path), &self.module_path.path),
            annotated,
        );
        traverse::super_value_binding(self, vb);
        let exceptions = self
            .find_local_path(&name_in_path)
            .cloned()
            .unwrap_or_default();
        let events = std::mem::replace(&mut self.current_events, old_events);
        self.checks.push(Check {
            events,
            loc: self.tree.loc(self.tree.ta.pattern(vb.vb_pat).pat_loc),
            loc_full: self.tree.loc(vb.vb_loc),
            module_name: self.module_name.to_string(),
            exn_name: name.to_string(),
            exceptions,
        });
        self.current_id = old_id;
    }

    /// `toplevel_eval`.
    fn toplevel_eval(&mut self, e: TExprIdx, attributes: &Attributes) {
        let name = "Toplevel expression";
        let old_id = self.current_id.replace(name.to_string());
        let old_events = std::mem::take(&mut self.current_events);
        self.expr(e);
        let events = std::mem::replace(&mut self.current_events, old_events);
        let loc = self.tree.loc(self.tree.ta.expr(e).exp_loc);
        self.checks.push(Check {
            events,
            loc,
            loc_full: loc,
            module_name: self.module_name.to_string(),
            exn_name: name.to_string(),
            exceptions: self.exceptions_from_annotations(attributes),
        });
        self.current_id = old_id;
    }

    /// `process_module_expr`: the module expression of a module binding,
    /// read in `module_path`.
    fn process_module_expr(&mut self, module_path: ModulePath, m: TModExprIdx) {
        match &self.tree.ta.module_expr(m).mod_desc {
            tt::ModuleExprDesc::Tmod_structure(structure) => {
                self.process_structure(module_path, structure)
            }
            tt::ModuleExprDesc::Tmod_constraint(inner, ..) => {
                self.process_module_expr(module_path, *inner)
            }
            tt::ModuleExprDesc::Tmod_apply(m1, m2, _) => {
                self.process_module_expr(module_path.clone(), *m1);
                self.process_module_expr(module_path, *m2);
            }
            tt::ModuleExprDesc::Tmod_ident(..)
            | tt::ModuleExprDesc::Tmod_functor(..)
            | tt::ModuleExprDesc::Tmod_unpack(..) => {
                let outer = std::mem::replace(&mut self.module_path, module_path);
                traverse::super_module_expr(self, m);
                self.module_path = outer;
            }
        }
    }

    /// A module binding of a structure read by `process_structure`: its
    /// expression is read inside the module, and a binding to a module path
    /// is an alias in the structure.
    fn module_binding(&mut self, mb: &'t tt::ModuleBinding) {
        let name = name_create(mb.mb_id.name(), true);
        let inside = self
            .module_path
            .enter_module(name.clone(), self.tree.loc(mb.mb_loc));
        self.process_module_expr(inside, mb.mb_expr);
        if let tt::ModuleExprDesc::Tmod_ident(path, _) =
            &self.tree.ta.module_expr(mb.mb_expr).mod_desc
        {
            self.add_alias(name, path_from_type_path(path));
        }
    }

    /// `process_structure`: the items of a structure, read in `module_path`.
    fn process_structure(&mut self, module_path: ModulePath, structure: &'t tt::Structure) {
        let outer = std::mem::replace(&mut self.module_path, module_path);
        for item in self.tree.ta.structure_items(structure.str_items) {
            match &item.str_desc {
                tt::StructureItemDesc::Tstr_eval(e, attributes) => {
                    self.toplevel_eval(*e, attributes)
                }
                tt::StructureItemDesc::Tstr_module(mb) => self.module_binding(mb),
                tt::StructureItemDesc::Tstr_recmodule(mbs) => {
                    for mb in mbs {
                        self.module_binding(mb);
                    }
                }
                _ => traverse::super_structure_item(self, item),
            }
        }
        self.module_path = outer;
    }
}

impl<'t> Visitor<'t> for Traverse<'t, '_, '_> {
    fn ta(&self) -> &'t tt::TypedArena {
        self.tree.ta
    }

    fn expr(&mut self, e: TExprIdx) {
        use tt::ExpressionDesc::*;
        let ta = self.tree.ta;
        let expr = ta.expr(e);
        let loc = self.tree.loc(expr.exp_loc);
        let is_does_not_throw = self.does_not_throw(ta.exp_attributes(expr));
        let old_events = is_does_not_throw.then(|| std::mem::take(&mut self.current_events));
        match &expr.exp_desc {
            Texp_ident(callee, _, _) => {
                let callee = self.resolve_alias(path_from_type_path(callee));
                let callee_name = path_to_string(&callee);
                if is_throw(&callee_name) {
                    self.log.warning(
                        loc,
                        Description::ExceptionAnalysis {
                            message: format!(
                                "{callee_name} can be analyzed only if called directly"
                            ),
                        },
                    );
                }
                let module_path = self.module_path.path.clone();
                self.push(
                    Exceptions::new(),
                    loc,
                    EventKind::Call {
                        callee,
                        module_path,
                    },
                );
            }
            Texp_apply { funct, args, .. } => match &ta.expr(*funct).exp_desc {
                Texp_ident(callee, _, _) => {
                    let callee_name = callee.name();
                    self.apply(&callee_name, *funct, ta.apply_args(*args), loc)
                }
                _ => traverse::super_expr(self, e),
            },
            Texp_match(scrutinee, value_cases, exn_cases, partial) => {
                let exn_cases = ta.cases(*exn_cases);
                if exn_cases.is_empty() {
                    self.expr(*scrutinee);
                } else {
                    let exceptions = self.exceptions_of_cases(exn_cases);
                    self.catches(*scrutinee, exceptions, loc);
                }
                self.cases(ta.cases(*value_cases));
                self.cases(exn_cases);
                if *partial == tt::Partial::Partial {
                    self.push(
                        Exceptions::from([MATCH_FAILURE.to_string()]),
                        loc,
                        EventKind::Throws,
                    );
                }
            }
            Texp_try(body, handlers, finally) => {
                let handlers = ta.cases(*handlers);
                // No exceptions means a catch-all, so a try without catch
                // cases must not record one.
                if handlers.is_empty() {
                    self.expr(*body);
                } else {
                    let exceptions = self.exceptions_of_cases(handlers);
                    self.catches(*body, exceptions, loc);
                }
                self.cases(handlers);
                self.expr_opt(*finally);
            }
            _ => traverse::super_expr(self, e),
        }
        if let Some(old_events) = old_events {
            let nested = std::mem::replace(&mut self.current_events, old_events);
            self.push(Exceptions::new(), loc, EventKind::DoesNotThrow(nested));
        }
    }

    fn value_binding(&mut self, vb: &'t tt::ValueBinding) {
        let ta = self.tree.ta;
        let is_function = matches!(
            ta.expr(vb.vb_expr).exp_desc,
            tt::ExpressionDesc::Texp_function { .. }
        );
        let is_toplevel = self.current_id.is_none();
        let ghost = self.tree.loc_ghost(vb.vb_loc);
        match &ta.pattern(vb.vb_pat).pat_desc {
            tt::PatternDesc::Tpat_any if is_toplevel && !ghost => self.process_binding("_", vb),
            tt::PatternDesc::Tpat_construct(lid, _, _)
                if is_toplevel && !ghost && self.tree.lid_string(lid.txt) == "()" =>
            {
                self.process_binding("()", vb)
            }
            tt::PatternDesc::Tpat_var(id, name)
                if (is_function || is_toplevel) && !self.tree.loc_ghost(name.loc) && !ghost =>
            {
                self.process_binding(id.name(), vb)
            }
            _ => traverse::super_value_binding(self, vb),
        }
    }
}

/// `Exception.process_cmt`: the annotations and checks of an
/// implementation.
pub fn process_structure<'t>(
    tree: &'t Tree<'t>,
    log: &mut Log<'_>,
    config: &Config,
    file: &'t FileContext,
    structure: &'t tt::Structure,
) -> FileResult {
    let mut traverse = Traverse {
        tree,
        log,
        debug: config.cli.debug,
        module_name: &file.module_name,
        module_path: ModulePath::initial(),
        current_id: None,
        current_events: Vec::new(),
        values: HashMap::new(),
        checks: Vec::new(),
    };
    traverse.process_structure(ModulePath::initial(), structure);
    FileResult {
        module_name: file.module_name.clone(),
        values: traverse.values,
        checks: traverse.checks,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn path(dotted: &str) -> DcePath {
        dotted
            .split('.')
            .rev()
            .map(|name| name_create(name, true))
            .collect()
    }

    #[test]
    fn an_alias_replaces_the_outermost_module_of_a_path() {
        let mut aliases = BTreeMap::new();
        aliases.insert(name_create("B", true), path("A.Inner"));
        // OCaml appends the alias's path, innermost name first, to the rest
        // of the path before reversing: the alias's names come out reversed.
        assert_eq!(
            path_to_string(&normalize_path(&aliases, path("B.f"), None)),
            "Inner.A.f"
        );
        assert_eq!(
            path_to_string(&normalize_path(&aliases, path("C.f"), None)),
            "C.f"
        );
        assert_eq!(
            path_to_string(&normalize_path(&aliases, path("B"), None)),
            "B"
        );
    }

    #[test]
    fn a_non_zero_literal_divisor_cannot_throw() {
        assert!(is_non_zero_constant(&tt::Constant::Int(10)));
        assert!(!is_non_zero_constant(&tt::Constant::Int(0)));
        assert!(is_non_zero_constant(&tt::Constant::Float(
            "1_0.5".to_string()
        )));
        assert!(!is_non_zero_constant(&tt::Constant::Float(
            "0.0".to_string()
        )));
        assert!(is_non_zero_constant(&tt::Constant::Float(
            "0x1p3".to_string()
        )));
        assert!(!is_non_zero_constant(&tt::Constant::BigInt(
            true,
            "000".to_string()
        )));
        assert!(is_non_zero_constant(&tt::Constant::BigInt(
            false,
            "102".to_string()
        )));
    }

    #[test]
    fn a_value_is_found_in_an_enclosing_module_then_in_another_file() {
        let mut here = HashMap::new();
        here.insert("M.f".to_string(), Exceptions::from(["A".to_string()]));
        let mut other = HashMap::new();
        other.insert("g".to_string(), Exceptions::from(["B".to_string()]));
        let table: ValuesTable<'_> = [("Here", &here), ("Other", &other)].into_iter().collect();
        let found = |module_path: &str, callee: &str| {
            let module_path = if module_path.is_empty() {
                Vec::new()
            } else {
                path(module_path)
            };
            find_path(&table, "Here", &module_path, &path(callee)).cloned()
        };
        assert_eq!(found("M.N", "f"), Some(Exceptions::from(["A".to_string()])));
        assert_eq!(found("", "M.f"), Some(Exceptions::from(["A".to_string()])));
        assert_eq!(
            found("M", "Other.g"),
            Some(Exceptions::from(["B".to_string()]))
        );
        assert_eq!(found("", "h"), None);
    }
}
