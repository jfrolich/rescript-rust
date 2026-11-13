//! The termination analysis: whether recursive functions annotated
//! `@progress` make progress before they recurse
//! (analysis/reanalyze/src/arnold.ml; analysis/reanalyze/TERMINATION.md
//! specifies it).
//!
//! Each group of recursive bindings with a `@progress` annotation is
//! compiled to commands: calls of the group's functions, calls of progress
//! functions, and how they combine. Running a function's commands on an
//! abstract state tells whether a call of the function is reached again
//! without progress in between, which is a possible infinite loop.
//!
//! OCaml also builds a trace of each run for debug messages that
//! `Log_.warning ~for_stats:false` then drops; the trace is not kept here.

use super::annotation::{self, AttributePayload};
use super::common::*;
use super::log::{Description, Log, Termination};
use super::ocaml_hash;
use super::traverse::{self, Visitor};
use crate::parser::ast::{Attributes, RecFlag};
use crate::types::asttypes::ArgLabel;
use crate::types::typedtree as tt;
use crate::types::typedtree::TExprIdx;
use indexmap::IndexMap;
use std::cell::OnceCell;
use std::collections::{BTreeSet, HashMap, VecDeque};

/// `Function_args.arg`: a function passed as the labeled argument `label`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct FunctionArg {
    label: String,
    function_name: String,
}

/// `Function_call.t`: a function and the functions it is instantiated with.
/// The derived order is `Function_call.compare`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct FunctionCall {
    function_name: String,
    function_args: Vec<FunctionArg>,
}

impl FunctionCall {
    fn no_args(function_name: &str) -> FunctionCall {
        FunctionCall {
            function_name: function_name.to_string(),
            function_args: Vec::new(),
        }
    }

    /// `Function_call.apply_substitution`: the call with the labels of
    /// `sub` replaced by the functions passed for them.
    fn apply_substitution(&self, sub: &[FunctionArg]) -> FunctionCall {
        let substitute = |name: &str| {
            sub.iter()
                .find(|arg| arg.label == name)
                .map_or_else(|| name.to_string(), |arg| arg.function_name.clone())
        };
        FunctionCall {
            function_name: substitute(&self.function_name),
            function_args: self
                .function_args
                .iter()
                .map(|arg| FunctionArg {
                    label: arg.label.clone(),
                    function_name: substitute(&arg.function_name),
                })
                .collect(),
        }
    }
}

impl std::fmt::Display for FunctionCall {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.function_name)?;
        if !self.function_args.is_empty() {
            let args: Vec<String> = self
                .function_args
                .iter()
                .map(|arg| format!("{}:{}", arg.label, arg.function_name))
                .collect();
            write!(f, "<{}>", args.join(","))?;
        }
        Ok(())
    }
}

/// The counters `Arnold.Stats` keeps over a run.
#[derive(Debug, Default)]
pub struct Stats {
    cache_checks: u32,
    cache_hits: u32,
    files: u32,
    functions: usize,
    hygiene_errors: u32,
    infinite_loops: u32,
    recursive_blocks: u32,
}

impl Stats {
    /// `Arnold.report_stats`.
    pub fn report(&self, log: &mut Log<'_>) {
        let dim = |n: String| log.tag("dim", &n);
        let text = format!(
            "\n  {}\n  Files:{}\n  Recursive Blocks:{}\n  Functions:{}\n  Infinite Loops:{}\n  Hygiene Errors:{}\n  Cache Hits:{}/{}\n  \n",
            log.tag("warning", "Termination Analysis Stats"),
            dim(self.files.to_string()),
            dim(self.recursive_blocks.to_string()),
            dim(self.functions.to_string()),
            dim(self.infinite_loops.to_string()),
            dim(self.hygiene_errors.to_string()),
            dim(self.cache_hits.to_string()),
            dim(self.cache_checks.to_string()),
        );
        log.print(&text);
    }
}

fn hygiene(log: &mut Log<'_>, stats: &mut Stats, loc: Loc, message: String) {
    stats.hygiene_errors += 1;
    log.error(
        loc,
        Description::Termination {
            termination: Termination::ErrorHygiene,
            message,
        },
    );
}

/// `Stats.log_hygiene_only_call_directly`.
fn only_call_directly(log: &mut Log<'_>, stats: &mut Stats, loc: Loc, name: &str) {
    hygiene(
        log,
        stats,
        loc,
        format!("{name} can only be called directly, or passed as labeled argument"),
    );
}

/// `Progress.t`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Progress {
    Progress,
    NoProgress,
}

/// `Call.t`.
#[derive(Debug, Clone)]
enum Call {
    FunctionCall(FunctionCall),
    /// A call of the progress function of this name.
    ProgressFunction(String),
}

/// `Values.t`: the progress made when a function returns `None` and when
/// it returns `Some`.
#[derive(Debug, Clone, Copy)]
struct Values {
    none: Option<Progress>,
    some: Option<Progress>,
}

impl Values {
    fn nd(v1: Values, v2: Values) -> Values {
        let combine = |x: Option<Progress>, y: Option<Progress>| match (x, y) {
            (Some(p1), Some(p2)) => Some(if p1 == Progress::Progress && p2 == Progress::Progress {
                Progress::Progress
            } else {
                Progress::NoProgress
            }),
            (None, p) | (p, None) => p,
        };
        Values {
            none: combine(v1.none, v2.none),
            some: combine(v1.some, v2.some),
        }
    }
}

/// `State.t`, without its trace.
#[derive(Debug, Clone, Copy)]
struct State {
    progress: Progress,
    values_opt: Option<Values>,
}

impl State {
    const INIT: State = State {
        progress: Progress::NoProgress,
        values_opt: None,
    };

    fn progress(progress: Progress) -> State {
        State {
            progress,
            values_opt: None,
        }
    }

    fn seq(s1: State, s2: State) -> State {
        State {
            progress: if s1.progress == Progress::Progress || s2.progress == Progress::Progress {
                Progress::Progress
            } else {
                Progress::NoProgress
            },
            values_opt: s2.values_opt,
        }
    }

    fn nd(s1: State, s2: State) -> State {
        let values_opt = match (s1.values_opt, s2.values_opt) {
            (None, values_opt) => (s1.progress == Progress::Progress)
                .then_some(values_opt)
                .flatten(),
            (values_opt, None) => (s2.progress == Progress::Progress)
                .then_some(values_opt)
                .flatten(),
            (Some(values1), Some(values2)) => Some(Values::nd(values1, values2)),
        };
        State {
            progress: if s1.progress == Progress::Progress && s2.progress == Progress::Progress {
                Progress::Progress
            } else {
                Progress::NoProgress
            },
            values_opt,
        }
    }

    /// `State.none` and `State.some`.
    fn option(some: bool, progress: Progress) -> State {
        State {
            progress,
            values_opt: Some(if some {
                Values {
                    none: None,
                    some: Some(progress),
                }
            } else {
                Values {
                    none: Some(progress),
                    some: None,
                }
            }),
        }
    }
}

/// `Command.t`.
#[derive(Debug, Clone)]
enum Command {
    Call(Call, Loc),
    /// The construction of `Some` (true) or `None`.
    ConstrOption(bool),
    Nondet(Vec<Command>),
    Nothing,
    Sequence(Vec<Command>),
    SwitchOption {
        function_call: FunctionCall,
        loc: Loc,
        some: Box<Command>,
        none: Box<Command>,
    },
    UnorderedSequence(Vec<Command>),
}

impl std::fmt::Display for Command {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let join = |commands: &[Command], separator: &str| {
            commands
                .iter()
                .map(Command::to_string)
                .collect::<Vec<_>>()
                .join(separator)
        };
        match self {
            Command::Call(Call::ProgressFunction(name), _) => write!(f, "+{name}"),
            Command::Call(Call::FunctionCall(function_call), _) => write!(f, "{function_call}"),
            Command::ConstrOption(some) => f.write_str(if *some { "Some" } else { "None" }),
            Command::Nondet(commands) => write!(f, "[{}]", join(commands, " || ")),
            Command::Nothing => f.write_str("_"),
            Command::Sequence(commands) => f.write_str(&join(commands, "; ")),
            Command::SwitchOption {
                function_call,
                some,
                none,
                ..
            } => write!(f, "switch {function_call} {{some: {some}, none: {none}}}"),
            Command::UnorderedSequence(commands) => write!(f, "{{{}}}", join(commands, ", ")),
        }
    }
}

impl Command {
    /// `Command.nondet`.
    fn nondet(mut commands: Vec<Command>) -> Command {
        loop {
            match commands.first() {
                None => return Command::Nothing,
                Some(Command::Nondet(_)) => {
                    let Command::Nondet(mut first) = commands.remove(0) else {
                        unreachable!()
                    };
                    first.append(&mut commands);
                    commands = first;
                }
                Some(_) if commands.len() == 1 => return commands.remove(0),
                Some(_) => return Command::Nondet(commands),
            }
        }
    }

    /// `Command.sequence`.
    fn sequence(commands: Vec<Command>) -> Command {
        let mut rest: VecDeque<Command> = commands.into();
        let mut kept: Vec<Command> = Vec::new();
        while let Some(command) = rest.pop_front() {
            match command {
                Command::Nothing if !rest.is_empty() => {}
                Command::Sequence(inner) => {
                    for command in inner.into_iter().rev() {
                        rest.push_front(command);
                    }
                }
                command => kept.push(command),
            }
        }
        if kept.len() == 1 {
            kept.remove(0)
        } else {
            Command::Sequence(kept)
        }
    }

    /// `c1 +++ c2`.
    fn then(self, next: Command) -> Command {
        Command::sequence(vec![self, next])
    }

    /// `Command.unordered_sequence`.
    fn unordered_sequence(commands: Vec<Command>) -> Command {
        let mut relevant: Vec<Command> = commands
            .into_iter()
            .filter(|command| !matches!(command, Command::Nothing))
            .collect();
        match relevant.len() {
            0 => Command::Nothing,
            1 => relevant.remove(0),
            _ => Command::UnorderedSequence(relevant),
        }
    }
}

/// `Kind.entry`: a labeled argument a function takes a recursive function
/// for. The derived order is the one `List.sort compare` gives.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct KindEntry {
    label: String,
    k: Vec<KindEntry>,
}

/// `Kind.to_string`.
fn kind_to_string(kind: &[KindEntry]) -> String {
    if kind.is_empty() {
        return String::new();
    }
    let entries: Vec<String> = kind
        .iter()
        .map(|entry| {
            if entry.k.is_empty() {
                entry.label.clone()
            } else {
                format!("{}:{}", entry.label, kind_to_string(&entry.k))
            }
        })
        .collect();
    format!("<{}>", entries.join(", "))
}

/// `Function_table.function_definition`.
#[derive(Debug, Default)]
struct FunctionDefinition {
    body: Option<Command>,
    kind: Vec<KindEntry>,
}

/// `Function_table.t`: the functions of a recursive group, in the order
/// they were added.
#[derive(Debug, Default)]
struct FunctionTable {
    functions: IndexMap<String, FunctionDefinition>,
}

impl FunctionTable {
    fn contains(&self, name: &str) -> bool {
        self.functions.contains_key(name)
    }

    /// `Function_table.add_function`.
    fn add_function(&mut self, name: &str) {
        self.functions
            .insert(name.to_string(), FunctionDefinition::default());
    }

    /// `Function_table.add_label_to_kind`.
    fn add_label_to_kind(&mut self, name: &str, label: &str) {
        if let Some(definition) = self.functions.get_mut(name)
            && !definition.kind.iter().any(|entry| entry.label == label)
        {
            definition.kind.push(KindEntry {
                label: label.to_string(),
                k: Vec::new(),
            });
            definition.kind.sort();
        }
    }

    /// `Function_table.function_get_kind_of_label`: whether `label` is a
    /// labeled argument `name` takes a recursive function for.
    fn has_label(&self, name: &str, label: &str) -> bool {
        self.functions
            .get(name)
            .is_some_and(|definition| definition.kind.iter().any(|entry| entry.label == label))
    }

    /// The table's functions in the order `Hashtbl.iter` visits them: OCaml
    /// compiles the functions of a group in this order, which is the order
    /// their errors are reported in. The table is made by `Hashtbl.create
    /// 1`, which has 16 buckets.
    fn hashtbl_order(&self) -> Vec<String> {
        let hashes: Vec<u32> = self
            .functions
            .keys()
            .map(|name| ocaml_hash::hash_string(name))
            .collect();
        ocaml_hash::iteration_order(16, &hashes)
            .into_iter()
            .filter_map(|i| self.functions.get_index(i))
            .map(|(name, _)| name.clone())
            .collect()
    }

    /// `Function_table.dump`.
    fn dump(&self, log: &mut Log<'_>) {
        let mut names: Vec<&String> = self.functions.keys().collect();
        names.sort();
        let mut out = format!("\n  {}", log.tag("warning", "Function Table"));
        for (i, name) in names.into_iter().enumerate() {
            let definition = &self.functions[name];
            out.push_str(&format!(
                "\n  {} {}: {}",
                log.tag("dim", &(i + 1).to_string()),
                log.tag(
                    "info",
                    &format!("{name}{}", kind_to_string(&definition.kind))
                ),
                definition
                    .body
                    .as_ref()
                    .map_or_else(|| "None".to_string(), Command::to_string)
            ));
        }
        out.push('\n');
        log.print(&out);
    }
}

/// What `value_bindings_table` holds for a variable: its definition and,
/// computed on demand, the functions its definition calls.
struct Binding {
    expr: TExprIdx,
    callees: OnceCell<BTreeSet<String>>,
}

/// `Find_functions_called`.
struct FindCallees<'t> {
    ta: &'t tt::TypedArena,
    callees: BTreeSet<String>,
}

impl<'t> Visitor<'t> for FindCallees<'t> {
    fn ta(&self) -> &'t tt::TypedArena {
        self.ta
    }

    fn expr(&mut self, e: TExprIdx) {
        let callee = match &self.ta.expr(e).exp_desc {
            tt::ExpressionDesc::Texp_apply { funct, .. } => Some(*funct),
            tt::ExpressionDesc::Texp_tagged_template { tag, .. } => Some(*tag),
            _ => None,
        };
        if let Some(callee) = callee
            && let tt::ExpressionDesc::Texp_ident(path, _, _) = &self.ta.expr(callee).exp_desc
        {
            self.callees.insert(path.name());
        }
        traverse::super_expr(self, e);
    }
}

impl Binding {
    /// `Find_functions_called.find_callees`: the functions a function's
    /// body calls; none for a definition that is no function.
    fn callees(&self, ta: &tt::TypedArena) -> &BTreeSet<String> {
        self.callees.get_or_init(|| {
            let mut find = FindCallees {
                ta,
                callees: BTreeSet::new(),
            };
            if matches!(
                ta.expr(self.expr).exp_desc,
                tt::ExpressionDesc::Texp_function { .. }
            ) {
                find.expr(self.expr);
            }
            find.callees
        })
    }
}

/// An argument of an application as the compiler reads it: one the source
/// writes, or the function an inner recursive function is implicitly passed
/// for the labeled argument of this name.
enum Arg<'t> {
    Written(&'t tt::ApplyArg),
    FromKind(String),
}

/// `Extend_function_table.extract_labelled_argument`: the function passed
/// as an argument, as its name and the location of its identifier. `kind`
/// is given when the argument may also be the application of a function to
/// arguments other than the ones of `kind`.
fn extract_labelled_argument(
    tree: &Tree<'_>,
    kind: Option<&[KindEntry]>,
    arg: Option<TExprIdx>,
) -> Option<(String, Loc)> {
    use tt::ExpressionDesc::*;
    let ta = tree.ta;
    let ident = |e: TExprIdx| match &ta.expr(e).exp_desc {
        Texp_ident(path, lid, _) => Some((path.name(), tree.loc(lid.loc))),
        _ => None,
    };
    match &ta.expr(arg?).exp_desc {
        Texp_ident(path, lid, _) => Some((path.name(), tree.loc(lid.loc))),
        Texp_let(RecFlag::Nonrecursive, vbs, _) => match ta.value_bindings(*vbs) {
            [vb] if matches!(
                ta.pattern(vb.vb_pat).pat_desc,
                tt::PatternDesc::Tpat_var(..)
            ) && tree.loc_ghost(vb.vb_loc) =>
            {
                ident(vb.vb_expr)
            }
            _ => None,
        },
        Texp_apply { funct, args, .. } => {
            let kind = kind?;
            let found = ident(*funct)?;
            let passes_no_kind_label = ta.apply_args(*args).iter().all(|arg| match &arg.label {
                ArgLabel::Labelled(l) | ArgLabel::Optional(l) => {
                    kind.iter().all(|entry| entry.label != l.txt)
                }
                ArgLabel::Nolabel => true,
            });
            passes_no_kind_label.then_some(found)
        }
        _ => None,
    }
}

/// `Extend_function_table`: add to the table the functions that call a
/// progress function, and the labeled arguments recursive functions are
/// passed for.
struct Extend<'a, 't> {
    tree: &'t Tree<'t>,
    table: &'a mut FunctionTable,
    progress_functions: &'a BTreeSet<String>,
    bindings: &'a HashMap<String, Binding>,
}

impl<'t> Visitor<'t> for Extend<'_, 't> {
    fn ta(&self) -> &'t tt::TypedArena {
        self.tree.ta
    }

    fn expr(&mut self, e: TExprIdx) {
        use tt::ExpressionDesc::*;
        let ta = self.tree.ta;
        match &ta.expr(e).exp_desc {
            Texp_ident(callee, _, _) => {
                let name = callee.name();
                if let Some(binding) = self.bindings.get(&name)
                    && !binding.callees(ta).is_disjoint(self.progress_functions)
                    && !self.table.contains(&name)
                {
                    self.table.add_function(&name);
                }
            }
            Texp_apply { funct, args, .. } => {
                if let Texp_ident(callee, _, _) = &ta.expr(*funct).exp_desc {
                    let function_name = callee.name();
                    if self.table.contains(&function_name) {
                        for arg in ta.apply_args(*args) {
                            if let ArgLabel::Labelled(label) = &arg.label
                                && let Some((passed, _)) =
                                    extract_labelled_argument(self.tree, None, arg.expression)
                                && self.table.contains(&passed)
                            {
                                self.table.add_label_to_kind(&function_name, &label.txt);
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        traverse::super_expr(self, e);
    }
}

/// `Check_expression_well_formed`: a function of the table is called
/// directly or passed as a labeled argument, nothing else.
struct Check<'a, 't, 'l, 'c> {
    tree: &'t Tree<'t>,
    table: &'a mut FunctionTable,
    bindings: &'a HashMap<String, Binding>,
    log: &'l mut Log<'c>,
    stats: &'a mut Stats,
}

impl Check<'_, '_, '_, '_> {
    fn check_ident(&mut self, name: &str, loc: Loc) {
        if self.table.contains(name) {
            only_call_directly(self.log, self.stats, loc, name);
        }
    }
}

impl<'t> Visitor<'t> for Check<'_, 't, '_, '_> {
    fn ta(&self) -> &'t tt::TypedArena {
        self.tree.ta
    }

    fn expr(&mut self, e: TExprIdx) {
        use tt::ExpressionDesc::*;
        let ta = self.tree.ta;
        match &ta.expr(e).exp_desc {
            Texp_ident(path, lid, _) => self.check_ident(&path.name(), self.tree.loc(lid.loc)),
            Texp_apply { funct, args, .. }
                if matches!(ta.expr(*funct).exp_desc, Texp_ident(..)) =>
            {
                let Texp_ident(function_path, _, _) = &ta.expr(*funct).exp_desc else {
                    unreachable!()
                };
                let function_name = function_path.name();
                for arg in ta.apply_args(*args) {
                    let Some((passed, loc)) =
                        extract_labelled_argument(self.tree, None, arg.expression)
                    else {
                        continue;
                    };
                    let ArgLabel::Labelled(label) = &arg.label else {
                        self.check_ident(&passed, loc);
                        continue;
                    };
                    if self.table.has_label(&function_name, &label.txt) {
                        continue;
                    }
                    if self.bindings.contains_key(&function_name) && self.table.contains(&passed) {
                        // A function defined before the group that is passed
                        // one of its functions is parametric.
                        if !self.table.contains(&function_name) {
                            self.table.add_function(&function_name);
                        }
                        self.table.add_label_to_kind(&function_name, &label.txt);
                    } else {
                        self.check_ident(&passed, loc);
                    }
                }
            }
            _ => traverse::super_expr(self, e),
        }
    }
}

/// `Compile`: the commands of a function's body.
struct Compile<'a, 't, 'l, 'c> {
    tree: &'t Tree<'t>,
    table: &'a mut FunctionTable,
    progress_functions: &'a BTreeSet<String>,
    /// The functions `let rec` binds inside the body, by the name the body
    /// calls them: the name they have in the table.
    inner_recursive_functions: HashMap<String, String>,
    log: &'l mut Log<'c>,
    stats: &'a mut Stats,
}

impl<'t> Compile<'_, 't, '_, '_> {
    fn not_implemented(&mut self, loc: Loc, case: &str) -> Command {
        // OCaml stops here with an assertion failure after reporting.
        self.log.error(
            loc,
            Description::Termination {
                termination: Termination::ErrorNotImplemented,
                message: case.to_string(),
            },
        );
        Command::Nothing
    }

    fn expression_opt(&mut self, current: &str, e: Option<TExprIdx>) -> Command {
        match e {
            Some(e) => self.expression(current, e),
            None => Command::Nothing,
        }
    }

    /// `e1 +++ e2`: OCaml evaluates the operands of `+++` right to left, so
    /// the second expression is compiled first; what compiling reports and
    /// registers follows that order.
    fn in_sequence(&mut self, current: &str, exprs: &[TExprIdx]) -> Command {
        let mut commands: Vec<Command> = exprs
            .iter()
            .rev()
            .map(|e| self.expression(current, *e))
            .collect();
        commands.reverse();
        Command::sequence(commands)
    }

    /// `eval_args`: the arguments in any order, then `command`.
    fn eval_args(&mut self, current: &str, args: &[Arg<'t>], command: Command) -> Command {
        let commands = args
            .iter()
            .map(|arg| match arg {
                Arg::Written(arg) => self.expression_opt(current, arg.expression),
                // The identifier of a function: nothing to evaluate.
                Arg::FromKind(_) => Command::Nothing,
            })
            .collect();
        Command::unordered_sequence(commands).then(command)
    }

    /// `case`.
    fn case(&mut self, current: &str, case: &tt::Case) -> Command {
        match case.c_guard {
            None => self.expression(current, case.c_rhs),
            Some(guard) => self.in_sequence(current, &[guard, case.c_rhs]),
        }
    }

    /// The function passed for the labeled argument `label` of a call of a
    /// function of the table (`get_function_arg`), or none after reporting
    /// why the call cannot be analyzed.
    fn function_arg(
        &mut self,
        current: &str,
        callee_kind: &[KindEntry],
        args: &[Arg<'t>],
        label: &str,
        loc: Loc,
    ) -> Option<FunctionArg> {
        let passed = args.iter().find_map(|arg| match arg {
            Arg::Written(tt::ApplyArg {
                label: ArgLabel::Labelled(l),
                expression: Some(e),
            }) if l.txt == label => Some(extract_labelled_argument(
                self.tree,
                Some(callee_kind),
                Some(*e),
            )),
            Arg::FromKind(l) if l == label => Some(Some((l.clone(), loc))),
            _ => None,
        });
        match passed.flatten() {
            None => {
                hygiene(
                    self.log,
                    self.stats,
                    loc,
                    format!("Call must have named argument {label}"),
                );
                None
            }
            Some((name, _))
                if self.table.contains(&name) || self.table.has_label(current, &name) =>
            {
                Some(FunctionArg {
                    label: label.to_string(),
                    function_name: name,
                })
            }
            Some(_) => {
                hygiene(
                    self.log,
                    self.stats,
                    loc,
                    format!("Named argument {label} must be passed a recursive function"),
                );
                None
            }
        }
    }

    /// The application of the value `callee_to_rename` names.
    fn apply(
        &mut self,
        current: &str,
        callee_to_rename: String,
        funct: TExprIdx,
        written: &'t [tt::ApplyArg],
        loc: Loc,
    ) -> Command {
        let mut args: Vec<Arg<'t>> = Vec::with_capacity(written.len());
        // An inner recursive function is called by the name it has in the
        // table, passed the functions its enclosing function is passed.
        let callee = match self.inner_recursive_functions.get(&callee_to_rename) {
            Some(inner) => {
                let inner = inner.clone();
                if let Some(definition) = self.table.functions.get(&inner) {
                    args.extend(
                        definition
                            .kind
                            .iter()
                            .map(|entry| Arg::FromKind(entry.label.clone())),
                    );
                }
                inner
            }
            None => callee_to_rename,
        };
        args.extend(written.iter().map(Arg::Written));
        if let Some(definition) = self.table.functions.get(&callee) {
            let kind = definition.kind.clone();
            let mut function_args = Vec::with_capacity(kind.len());
            for entry in &kind {
                match self.function_arg(current, &kind, &args, &entry.label, loc) {
                    Some(arg) => function_args.push(arg),
                    None => return Command::Nothing,
                }
            }
            let call = Call::FunctionCall(FunctionCall {
                function_name: callee,
                function_args,
            });
            self.eval_args(current, &args, Command::Call(call, loc))
        } else if self.progress_functions.contains(&callee) {
            self.eval_args(
                current,
                &args,
                Command::Call(Call::ProgressFunction(callee), loc),
            )
        } else if self.table.has_label(current, &callee) {
            let call = Call::FunctionCall(FunctionCall::no_args(&callee));
            self.eval_args(current, &args, Command::Call(call, loc))
        } else {
            let command = self.expression(current, funct);
            self.eval_args(current, &args, command)
        }
    }

    /// `Compile.expression`: the commands of `e` in the function `current`.
    fn expression(&mut self, current: &str, e: TExprIdx) -> Command {
        use tt::ExpressionDesc::*;
        let ta = self.tree.ta;
        let expr = ta.expr(e);
        let loc = self.tree.loc(expr.exp_loc);
        let written = |list: tt::TExprList| ta.expr_list(list);
        match &expr.exp_desc {
            Texp_ident(..) | Texp_constant(_) | Texp_assert(_) => Command::Nothing,
            Texp_apply { funct, args, .. } => match &ta.expr(*funct).exp_desc {
                Texp_ident(callee, _, _) => {
                    self.apply(current, callee.name(), *funct, ta.apply_args(*args), loc)
                }
                _ => {
                    let command = self.expression(current, *funct);
                    let args: Vec<Arg<'t>> =
                        ta.apply_args(*args).iter().map(Arg::Written).collect();
                    self.eval_args(current, &args, command)
                }
            },
            Texp_tagged_template { tag, values, .. } => {
                let command = self.expression(current, *tag);
                let commands = written(*values)
                    .iter()
                    .map(|value| self.expression(current, *value))
                    .collect();
                Command::unordered_sequence(commands).then(command)
            }
            Texp_template { values, .. } => Command::sequence(
                written(*values)
                    .iter()
                    .map(|value| self.expression(current, *value))
                    .collect(),
            ),
            Texp_let(rec_flag, vbs, in_expr) => {
                let vbs = ta.value_bindings(*vbs);
                if *rec_flag == RecFlag::Recursive
                    && let [vb] = vbs
                    && let tt::PatternDesc::Tpat_var(id, _) = &ta.pattern(vb.vb_pat).pat_desc
                {
                    // The function is added to the table as
                    // `<enclosing>$<name>`, taking the functions its
                    // enclosing function is passed.
                    let old_function_name = id.name().to_string();
                    let new_function_name = format!("{current}${old_function_name}");
                    self.table.add_function(&new_function_name);
                    let kind = self
                        .table
                        .functions
                        .get(current)
                        .map(|definition| definition.kind.clone())
                        .unwrap_or_default();
                    if let Some(definition) = self.table.functions.get_mut(&new_function_name) {
                        definition.kind = kind;
                    }
                    self.inner_recursive_functions
                        .insert(old_function_name, new_function_name.clone());
                    let body = self.expression(&new_function_name, vb.vb_expr);
                    if let Some(definition) = self.table.functions.get_mut(&new_function_name) {
                        definition.body = Some(body);
                    }
                    return self.expression(current, *in_expr);
                }
                if *rec_flag == RecFlag::Recursive {
                    hygiene(
                        self.log,
                        self.stats,
                        loc,
                        "Nested multiple let rec not supported yet".to_string(),
                    );
                }
                // `bindings @ [body]`: OCaml evaluates the operands of `@`
                // right to left, so the body is compiled first.
                let body = self.expression(current, *in_expr);
                let mut commands: Vec<Command> = vbs
                    .iter()
                    .map(|vb| self.expression(current, vb.vb_expr))
                    .collect();
                commands.push(body);
                Command::sequence(commands)
            }
            Texp_sequence(e1, e2)
            | Texp_for_of(_, _, e1, e2)
            | Texp_for_await_of(_, _, e1, e2)
            | Texp_object_set(e1, _, e2) => self.in_sequence(current, &[*e1, *e2]),
            Texp_for(_, _, e1, e2, _, e3) => self.in_sequence(current, &[*e1, *e2, *e3]),
            Texp_ifthenelse(e1, e2, e3) => {
                let c1 = self.expression(current, *e1);
                let c2 = self.expression(current, *e2);
                let c3 = self.expression_opt(current, *e3);
                c1.then(Command::nondet(vec![c2, c3]))
            }
            Texp_construct(lid, constructor, expressions) => {
                let commands = written(*expressions)
                    .iter()
                    .map(|e| self.expression(current, *e))
                    .collect();
                let c = Command::unordered_sequence(commands);
                let written_by_source = !self.tree.loc_ghost(lid.loc);
                match constructor.cstr_name.as_str() {
                    "Some" if written_by_source => c.then(Command::ConstrOption(true)),
                    "None" if written_by_source => c.then(Command::ConstrOption(false)),
                    _ => c,
                }
            }
            Texp_function { body, .. } => self.expression(current, *body),
            Texp_match(scrutinee, value_cases, exn_cases, _) => {
                if !ta.cases(*exn_cases).is_empty() {
                    return self.not_implemented(loc, "Texp_match with exception cases");
                }
                let cases = ta.cases(*value_cases);
                let c_e = self.expression(current, *scrutinee);
                let mut c_cases: Vec<Command> =
                    cases.iter().map(|case| self.case(current, case)).collect();
                let option_case = |case: &tt::Case| match &ta.pattern(case.c_lhs).pat_desc {
                    tt::PatternDesc::Tpat_construct(_, constructor, _) => {
                        match constructor.cstr_name.as_str() {
                            "Some" => Some(true),
                            "None" => Some(false),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                // A switch on the optional result of a function of the
                // table: each branch runs with the progress of that result.
                if let Command::Call(Call::FunctionCall(function_call), loc) = &c_e
                    && let [case1, case2] = cases
                    && let (Some(first_is_some), Some(_)) = (option_case(case1), option_case(case2))
                {
                    let second = c_cases.pop().unwrap_or(Command::Nothing);
                    let first = c_cases.pop().unwrap_or(Command::Nothing);
                    let (some, none) = if first_is_some {
                        (first, second)
                    } else {
                        (second, first)
                    };
                    return Command::SwitchOption {
                        function_call: function_call.clone(),
                        loc: *loc,
                        some: Box::new(some),
                        none: Box::new(none),
                    };
                }
                c_e.then(Command::nondet(c_cases))
            }
            Texp_field(e, _, _) | Texp_object_get(e, _) => self.expression(current, *e),
            Texp_record {
                fields,
                extended_expression,
                ..
            } => {
                let mut commands = vec![self.expression_opt(current, *extended_expression)];
                for (_, _, e) in ta.record_fields(*fields) {
                    commands.push(self.expression(current, *e));
                }
                Command::unordered_sequence(commands)
            }
            Texp_setfield(e1, _, _, e2) => {
                let commands = vec![self.expression(current, *e1), self.expression(current, *e2)];
                Command::unordered_sequence(commands)
            }
            Texp_tuple(expressions) | Texp_array(expressions) | Texp_spread(_, expressions) => {
                let commands = written(*expressions)
                    .iter()
                    .map(|e| self.expression(current, *e))
                    .collect();
                Command::unordered_sequence(commands)
            }
            Texp_dict(entries) => {
                let commands = ta
                    .dict_entries(*entries)
                    .iter()
                    .map(|entry| match entry {
                        tt::DictEntry::Tdict_entry(_, e) | tt::DictEntry::Tdict_spread(e) => {
                            self.expression(current, *e)
                        }
                    })
                    .collect();
                Command::unordered_sequence(commands)
            }
            Texp_try(body, handlers, finally) => {
                let c_e = self.expression(current, *body);
                let c_cases = Command::nondet(
                    ta.cases(*handlers)
                        .iter()
                        .map(|case| self.case(current, case))
                        .collect(),
                );
                match finally {
                    None => c_e.then(c_cases),
                    Some(finally) => {
                        let c_finally = self.expression(current, *finally);
                        c_e.then(c_cases).then(c_finally)
                    }
                }
            }
            Texp_variant(_, e) => self.expression_opt(current, *e),
            // Fields are evaluated in source order.
            Texp_object_literal(fields) => Command::sequence(
                fields
                    .iter()
                    .map(|(_, e)| self.expression(current, *e))
                    .collect(),
            ),
            Texp_while(..) => self.not_implemented(loc, "Texp_while"),
            Texp_letmodule(..) => self.not_implemented(loc, "Texp_letmodule"),
            Texp_letexception(..) => self.not_implemented(loc, "Texp_letexception"),
            Texp_pack(_) => self.not_implemented(loc, "Texp_pack"),
            Texp_break | Texp_continue => self.not_implemented(loc, "Texp_break | Texp_continue"),
        }
    }
}

/// `Call_stack.t`: the calls being run, each with its depth and where it
/// was made.
#[derive(Debug, Default)]
struct CallStack {
    frames: HashMap<FunctionCall, (usize, Pos)>,
    size: usize,
}

impl CallStack {
    fn add(&mut self, function_call: FunctionCall, pos: Pos) {
        self.size += 1;
        self.frames.insert(function_call, (self.size, pos));
    }

    fn remove(&mut self, function_call: &FunctionCall) {
        self.size -= 1;
        self.frames.remove(function_call);
    }

    /// `Call_stack.print`: the frames, the innermost first.
    fn print(&self, files: &Files) -> String {
        let mut frames: Vec<(&FunctionCall, usize, Pos)> = self
            .frames
            .iter()
            .map(|(function_call, (i, pos))| (function_call, *i, *pos))
            .collect();
        frames.sort_by(|(call1, i1, _), (call2, i2, _)| i2.cmp(i1).then_with(|| call1.cmp(call2)));
        let mut out = "  CallStack:".to_string();
        for (function_call, i, pos) in frames {
            out.push_str(&format!(
                "\n    {i} {function_call} ({} {})",
                basename(&files.name(pos.file)),
                pos.lnum
            ));
        }
        out
    }
}

/// The message of a possible infinite loop: the call, then the call
/// stack on its own lines. OCaml separates them with a break hint that
/// `Format` always breaks at: nothing after the hint tells its size before
/// the message is flushed, which counts it as not fitting on the line.
fn infinite_loop_message(
    function_call_to_instantiate: &FunctionCall,
    function_call: &FunctionCall,
    call_stack: &str,
) -> String {
    let mut message = format!("Possible infinite loop when calling {function_call_to_instantiate}");
    if function_call_to_instantiate != function_call {
        message.push_str(&format!(" which is {function_call}"));
    }
    message.push('\n');
    message.push_str(call_stack);
    message
}

/// `Eval`: runs the commands of the functions of a table.
struct Eval<'a, 'l, 'c> {
    table: &'a FunctionTable,
    cache: HashMap<FunctionCall, State>,
    files: &'a Files,
    log: &'l mut Log<'c>,
    stats: &'a mut Stats,
}

impl Eval<'_, '_, '_> {
    /// `Eval.run_function_call`: the state after calling
    /// `function_call_to_instantiate`, whose labels stand for
    /// `function_args`, in `state`.
    fn run_function_call(
        &mut self,
        function_call_to_instantiate: &FunctionCall,
        loc: Loc,
        call_stack: &mut CallStack,
        function_args: &[FunctionArg],
        made_progress_on: &BTreeSet<FunctionCall>,
        state: State,
    ) -> State {
        let function_call = function_call_to_instantiate.apply_substitution(function_args);
        let state_after_call = if let Some(cached) = self.cache.get(&function_call) {
            self.stats.cache_checks += 1;
            self.stats.cache_hits += 1;
            *cached
        } else if made_progress_on.contains(&function_call) {
            State::progress(Progress::Progress)
        } else if call_stack.frames.contains_key(&function_call) {
            // The call is being run already: a loop, and an infinite one
            // unless progress was made since.
            if state.progress == Progress::NoProgress {
                let message = infinite_loop_message(
                    function_call_to_instantiate,
                    &function_call,
                    &call_stack.print(self.files),
                );
                self.log.error(
                    loc,
                    Description::Termination {
                        termination: Termination::ErrorTermination,
                        message,
                    },
                );
                self.stats.infinite_loops += 1;
            }
            state
        } else {
            self.stats.cache_checks += 1;
            let table = self.table;
            let body = table
                .functions
                .get(&function_call.function_name)
                .and_then(|definition| definition.body.as_ref());
            call_stack.add(function_call.clone(), loc.start);
            let state_after_call = match body {
                Some(body) => self.run(
                    body,
                    call_stack,
                    &function_call.function_args,
                    made_progress_on,
                    State::INIT,
                ),
                None => State::INIT,
            };
            self.cache
                .entry(function_call.clone())
                .or_insert(state_after_call);
            call_stack.remove(&function_call);
            state_after_call
        };
        State::seq(state, state_after_call)
    }

    /// `Eval.run`: the state after running `command` in `state`.
    fn run(
        &mut self,
        command: &Command,
        call_stack: &mut CallStack,
        function_args: &[FunctionArg],
        made_progress_on: &BTreeSet<FunctionCall>,
        state: State,
    ) -> State {
        match command {
            Command::Call(Call::FunctionCall(function_call), loc) => self.run_function_call(
                function_call,
                *loc,
                call_stack,
                function_args,
                made_progress_on,
                state,
            ),
            Command::Call(Call::ProgressFunction(_), _) => {
                State::seq(state, State::progress(Progress::Progress))
            }
            Command::ConstrOption(some) => State::seq(state, State::option(*some, state.progress)),
            Command::Nothing => State::seq(state, State::INIT),
            Command::Sequence(commands) => {
                // Once a command makes progress, the calls being run have
                // made progress too: a later call of one is no loop.
                let mut state = state;
                let mut made_progress_on = std::borrow::Cow::Borrowed(made_progress_on);
                let mut fresh_call_stack: Option<CallStack> = None;
                for command in commands {
                    let current = match fresh_call_stack.as_mut() {
                        Some(call_stack) => call_stack,
                        None => &mut *call_stack,
                    };
                    state = self.run(command, current, function_args, &made_progress_on, state);
                    if state.progress == Progress::Progress {
                        made_progress_on
                            .to_mut()
                            .extend(current.frames.keys().cloned());
                        fresh_call_stack = Some(CallStack::default());
                    }
                }
                state
            }
            Command::UnorderedSequence(commands) => {
                // The commands run in any order: progress if any makes it.
                let mut states = commands
                    .iter()
                    .map(|c| self.run(c, call_stack, function_args, made_progress_on, state));
                let first = states.next().unwrap_or(State::INIT);
                let combined = states.fold(first, State::seq);
                State::seq(
                    state,
                    State {
                        values_opt: None,
                        ..combined
                    },
                )
            }
            Command::Nondet(commands) => {
                // One of the commands runs: progress if all make it.
                let mut states = commands
                    .iter()
                    .map(|c| self.run(c, call_stack, function_args, made_progress_on, state));
                let first = states.next().unwrap_or(State::INIT);
                State::seq(state, states.fold(first, State::nd))
            }
            Command::SwitchOption {
                function_call,
                loc,
                some,
                none,
            } => {
                let state_after_call = self.run_function_call(
                    function_call,
                    *loc,
                    call_stack,
                    function_args,
                    made_progress_on,
                    state,
                );
                match state_after_call.values_opt {
                    None => {
                        let branches = Command::nondet(vec![(**some).clone(), (**none).clone()]);
                        self.run(
                            &branches,
                            call_stack,
                            function_args,
                            made_progress_on,
                            state_after_call,
                        )
                    }
                    Some(values) => {
                        // A result the function never returns is not
                        // reached: its branch counts as progress.
                        let mut run_opt =
                            |command: &Command, progress: Option<Progress>| match progress {
                                None => State::progress(Progress::Progress),
                                Some(progress) => self.run(
                                    command,
                                    call_stack,
                                    function_args,
                                    made_progress_on,
                                    State::progress(progress),
                                ),
                            };
                        let state_none = run_opt(none, values.none);
                        let state_some = run_opt(some, values.some);
                        State::seq(state_after_call, State::nd(state_some, state_none))
                    }
                }
            }
        }
    }

    /// `Eval.analyze_function`.
    fn analyze_function(&mut self, debug: bool, function_name: &str, loc: Loc) {
        if debug {
            let text = format!(
                "\n  {} for {}\n",
                self.log.tag("warning", "Termination Analysis"),
                self.log.tag("info", function_name)
            );
            self.log.print(&text);
        }
        let function_call = FunctionCall::no_args(function_name);
        let mut call_stack = CallStack::default();
        call_stack.add(function_call.clone(), loc.start);
        let table = self.table;
        let Some(definition) = table.functions.get(function_name) else {
            return;
        };
        if !definition.kind.is_empty() {
            hygiene(
                self.log,
                self.stats,
                loc,
                format!("{function_name} cannot be analyzed directly as it is parametric"),
            );
            return;
        }
        let state = match &definition.body {
            Some(body) => self.run(body, &mut call_stack, &[], &BTreeSet::new(), State::INIT),
            None => State::INIT,
        };
        self.cache.entry(function_call).or_insert(state);
    }
}

/// `progress_functions_from_attributes`: the progress functions a
/// `@progress` annotation names, or none without the annotation.
fn progress_functions_from_attributes(
    tree: &Tree<'_>,
    attributes: &Attributes,
) -> Option<Vec<String>> {
    let payload =
        annotation::get_attribute_payload(tree.arena, |s| s == "progress", attributes.iter())?;
    Some(match payload {
        AttributePayload::Ident(name) => vec![name],
        AttributePayload::Tuple(payloads) => payloads
            .into_iter()
            .filter_map(|payload| match payload {
                AttributePayload::Ident(name) => Some(name),
                _ => None,
            })
            .collect(),
        _ => Vec::new(),
    })
}

/// `Arnold.traverse_ast`'s state.
struct Traverse<'t, 'l, 'c, 's> {
    tree: &'t Tree<'t>,
    log: &'l mut Log<'c>,
    stats: &'s mut Stats,
    debug: bool,
    /// `value_bindings_table`: the latest binding of each variable name.
    bindings: HashMap<String, Binding>,
}

impl<'t> Traverse<'t, '_, '_, '_> {
    /// Analyze a group of recursive bindings of which `functions_to_analyze`
    /// are annotated `@progress`.
    fn analyze_group(
        &mut self,
        vbs: &'t [tt::ValueBinding],
        progress_functions: &BTreeSet<String>,
        functions_to_analyze: &[(String, Loc)],
    ) {
        let ta = self.tree.ta;
        let mut table = FunctionTable::default();
        let recursive_definitions: Vec<(String, TExprIdx)> = vbs
            .iter()
            .filter_map(|vb| match &ta.pattern(vb.vb_pat).pat_desc {
                tt::PatternDesc::Tpat_var(id, _) => {
                    let binding = self.bindings.get(id.name())?;
                    Some((id.name().to_string(), binding.expr))
                }
                _ => None,
            })
            .collect();
        for (function_name, _) in &recursive_definitions {
            table.add_function(function_name);
        }
        for (_, body) in &recursive_definitions {
            let mut extend = Extend {
                tree: self.tree,
                table: &mut table,
                progress_functions,
                bindings: &self.bindings,
            };
            extend.expr(*body);
        }
        for (_, body) in &recursive_definitions {
            let mut check = Check {
                tree: self.tree,
                table: &mut table,
                bindings: &self.bindings,
                log: self.log,
                stats: self.stats,
            };
            check.expr(*body);
        }
        for function_name in table.hashtbl_order() {
            let has_body = table
                .functions
                .get(&function_name)
                .is_some_and(|definition| definition.body.is_some());
            if has_body {
                continue;
            }
            let Some(binding) = self.bindings.get(&function_name) else {
                continue;
            };
            let mut compile = Compile {
                tree: self.tree,
                table: &mut table,
                progress_functions,
                inner_recursive_functions: HashMap::new(),
                log: self.log,
                stats: self.stats,
            };
            let body = compile.expression(&function_name, binding.expr);
            if let Some(definition) = table.functions.get_mut(&function_name) {
                definition.body = Some(body);
            }
        }
        if self.debug {
            table.dump(self.log);
        }
        let mut eval = Eval {
            table: &table,
            cache: HashMap::new(),
            files: self.tree.files,
            log: self.log,
            stats: self.stats,
        };
        for (function_name, loc) in functions_to_analyze {
            eval.analyze_function(self.debug, function_name, *loc);
        }
        self.stats.recursive_blocks += 1;
        self.stats.functions += table.functions.len();
    }
}

impl<'t> Visitor<'t> for Traverse<'t, '_, '_, '_> {
    fn ta(&self) -> &'t tt::TypedArena {
        self.tree.ta
    }

    fn value_bindings(&mut self, rec_flag: RecFlag, vbs: &'t [tt::ValueBinding]) {
        let ta = self.tree.ta;
        for vb in vbs {
            if let tt::PatternDesc::Tpat_var(id, _) = &ta.pattern(vb.vb_pat).pat_desc {
                self.bindings.insert(
                    id.name().to_string(),
                    Binding {
                        expr: vb.vb_expr,
                        callees: OnceCell::new(),
                    },
                );
            }
        }
        if rec_flag == RecFlag::Recursive {
            let mut progress_functions: BTreeSet<String> = BTreeSet::new();
            let mut functions_to_analyze: Vec<(String, Loc)> = Vec::new();
            for vb in vbs {
                let Some(names) = progress_functions_from_attributes(self.tree, &vb.vb_attributes)
                else {
                    continue;
                };
                progress_functions.extend(names);
                if let tt::PatternDesc::Tpat_var(id, _) = &ta.pattern(vb.vb_pat).pat_desc {
                    let loc = self.tree.loc(ta.expr(vb.vb_expr).exp_loc);
                    functions_to_analyze.push((id.name().to_string(), loc));
                }
            }
            if !functions_to_analyze.is_empty() {
                self.analyze_group(vbs, &progress_functions, &functions_to_analyze);
            }
        }
        for vb in vbs {
            traverse::super_value_binding(self, vb);
        }
    }
}

/// `Arnold.process_cmt`: analyze the recursive functions of an
/// implementation.
pub fn process_structure<'t>(
    tree: &'t Tree<'t>,
    log: &mut Log<'_>,
    config: &Config,
    stats: &mut Stats,
    structure: &'t tt::Structure,
) {
    stats.files += 1;
    let mut traverse = Traverse {
        tree,
        log,
        stats,
        debug: config.cli.debug,
        bindings: HashMap::new(),
    };
    traverse.structure(structure);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn call(name: &str) -> Command {
        Command::Call(Call::FunctionCall(FunctionCall::no_args(name)), Loc::NONE)
    }

    #[test]
    fn commands_combine_as_in_ocaml() {
        let progress = || Command::Call(Call::ProgressFunction("progress".to_string()), Loc::NONE);
        // A trailing `Nothing` stays; inner ones and nested sequences do not.
        let sequence = Command::sequence(vec![
            Command::Nothing,
            Command::sequence(vec![progress(), call("f")]),
            Command::Nothing,
        ]);
        assert_eq!(sequence.to_string(), "+progress; f; _");
        assert_eq!(
            Command::sequence(vec![Command::Nothing, call("f")]).to_string(),
            "f"
        );
        // Only a leading nondeterministic choice is flattened.
        let nondet = Command::nondet(vec![Command::nondet(vec![call("a"), call("b")]), call("c")]);
        assert_eq!(nondet.to_string(), "[a || b || c]");
        assert_eq!(Command::nondet(vec![]).to_string(), "_");
        let unordered = Command::unordered_sequence(vec![call("a"), Command::Nothing, progress()]);
        assert_eq!(unordered.to_string(), "{a, +progress}");
    }

    #[test]
    fn a_loop_message_names_the_call_then_the_call_stack() {
        let f = FunctionCall::no_args("f");
        assert_eq!(
            infinite_loop_message(&f, &f, "  CallStack:\n    1 f (A.res 1)"),
            "Possible infinite loop when calling f\n  CallStack:\n    1 f (A.res 1)"
        );
        let instantiated = FunctionCall {
            function_name: "loop".to_string(),
            function_args: vec![FunctionArg {
                label: "f".to_string(),
                function_name: "parseInt".to_string(),
            }],
        };
        assert_eq!(
            infinite_loop_message(&f, &instantiated, "  CallStack:"),
            "Possible infinite loop when calling f which is loop<f:parseInt>\n  CallStack:"
        );
    }

    #[test]
    fn a_call_without_progress_in_between_loops() {
        let mut table = FunctionTable::default();
        table.add_function("f");
        table.functions["f"].body = Some(call("f"));
        let files = Files::new();
        let config = Config::default();
        let mut log = Log::new(&config, &files, false);
        let mut stats = Stats::default();
        let mut eval = Eval {
            table: &table,
            cache: HashMap::new(),
            files: &files,
            log: &mut log,
            stats: &mut stats,
        };
        eval.analyze_function(false, "f", Loc::NONE);
        assert_eq!(stats.infinite_loops, 1);

        // With progress before the recursive call there is no loop.
        let mut table = FunctionTable::default();
        table.add_function("g");
        table.functions["g"].body = Some(Command::sequence(vec![
            Command::Call(Call::ProgressFunction("progress".to_string()), Loc::NONE),
            call("g"),
        ]));
        let mut stats = Stats::default();
        let mut eval = Eval {
            table: &table,
            cache: HashMap::new(),
            files: &files,
            log: &mut log,
            stats: &mut stats,
        };
        eval.analyze_function(false, "g", Loc::NONE);
        assert_eq!(stats.infinite_loops, 0);
    }
}
