//! The naming log (THREE_TREES section 2 and 11.4, "T5 design" (e)): the
//! events from which `emit::naming::replay` assigns printed names when a
//! function scope closes, without a walk of the finished tree. The rule is
//! the header of `emit/naming.rs` (legacy `JsPrinter`,
//! compiler/ext/ext_pp_scope.ml: add_ident, merge, sub_scope); that pass
//! stays the oracle.
//!
//! The lowering does not call the log yet (THREE_TREES 11.7, step 4); the
//! module is compiled for tests only until then.
use crate::bir::{FuncId, NodeId, VarId, VarTable};

/// What an event names. The discriminant is the low three bits of
/// `Event::bits`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub(crate) enum EventKind {
    /// A declaration: the binder is named before its initialiser. Payload:
    /// the variable.
    Declare = 0,
    /// The parameters of the open function, in order. Payload: the function.
    Params = 1,
    /// A function literal: its free variables and its own binder are
    /// reserved in the enclosing scope, then a scope opens that inherits
    /// their suffix tables. Payload: the row of `Log::scopes`.
    Enter = 2,
    /// The open function closes. Payload: the row of `Log::scopes`.
    Leave = 3,
    /// A loop or catch variable, named before its body. Payload: the
    /// variable.
    Binder = 4,
}

/// One naming event, in the order the printer names. `statement` is the
/// statement the event belongs to: an event whose statement is not in the
/// final list is skipped by the replay, so a statement removed at a scope
/// close takes its events with it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Event {
    bits: u32,
    pub(crate) statement: NodeId,
}
impl Event {
    /// Constant.
    pub(crate) fn new(kind: EventKind, payload: u32, statement: NodeId) -> Self {
        assert!(payload < 1 << 29, "naming event payload");
        Self { bits: payload << 3 | kind as u32, statement }
    }
    /// Constant.
    pub(crate) fn kind(self) -> EventKind {
        match self.bits & 7 {
            0 => EventKind::Declare,
            1 => EventKind::Params,
            2 => EventKind::Enter,
            3 => EventKind::Leave,
            _ => EventKind::Binder,
        }
    }
    /// Constant.
    pub(crate) fn payload(self) -> u32 {
        self.bits >> 3
    }
    /// The variable of a `Declare` or `Binder`. Constant.
    pub(crate) fn var(self) -> VarId {
        VarId(self.payload())
    }
    /// The function of a `Params`. Constant.
    pub(crate) fn function(self) -> FuncId {
        FuncId(self.payload())
    }
}

/// One function scope: its header and its free variables as a run of
/// `Log::free` (final when the scope has closed, sorted by the variable's
/// `order`, then name: `Ident`'s order).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ScopeRow {
    pub(crate) function: FuncId,
    pub(crate) free_start: u32,
    pub(crate) free_len: u32,
}

/// The log of one unit. The program is the scope that is open when no
/// function is.
#[derive(Default)]
pub(crate) struct Log {
    pub(crate) events: Vec<Event>,
    pub(crate) scopes: Vec<ScopeRow>,
    /// The free-variable lists of the closed scopes, back to back.
    pub(crate) free: Vec<VarId>,
    /// The rows of the open scopes, innermost last.
    open: Vec<u32>,
    /// The variables referenced or declared in the open scopes, innermost
    /// run last; `marks` gives where each open scope's run starts.
    seen: Vec<VarId>,
    marks: Vec<u32>,
    /// One bit per variable: it is in the innermost open scope's run of
    /// `seen`. Dense by VarId.
    member: Vec<u64>,
    /// One bit per variable: the innermost open scope declares it.
    bound: Vec<u64>,
    /// Events logged, membership bits tested, and variables handed to an
    /// enclosing scope at a close.
    pub(crate) steps: usize,
}

impl Log {
    /// The statement of a `Leave`: it closes the `Enter` it matches and is
    /// read with it, never on its own.
    pub(crate) const NO_STATEMENT: NodeId = NodeId(u32::MAX);

    /// A log for a unit of `variables` variables, with the program scope
    /// open. Cost: two bits per variable, allocated once.
    pub(crate) fn new(variables: usize) -> Self {
        let words = variables.div_ceil(64);
        Self { member: vec![0; words], bound: vec![0; words], ..Self::default() }
    }

    /// Log `Declare(var)` for `statement` and mark `var` bound in the open
    /// scope (naming.rs `stmt`, `StmtKind::Variable`: the binder before the
    /// initialiser; for a function declaration the caller logs `enter`
    /// first unless the function is eta-reduced, `function`). Cost: one
    /// push and two bit writes; one step.
    pub(crate) fn declare(&mut self, var: VarId, statement: NodeId) {
        let binder = self.binds_function(statement);
        self.log(EventKind::Declare, var.0, statement);
        // The program scope keeps no run: nothing is free in it.
        if self.open.is_empty() {
            return;
        }
        if binder {
            // The binder of the function declaration just entered binds in
            // the enclosing scope; the open run is still empty.
            if self.open.len() > 1 {
                set(&mut self.bound, var);
            }
            return;
        }
        set(&mut self.bound, var);
        self.join(var);
    }

    /// Whether a `Declare` of `statement` logged now is the binder of the
    /// function declaration it follows: the last two events are that
    /// function's `Enter` and `Params`. Constant.
    fn binds_function(&self, statement: NodeId) -> bool {
        matches!(self.events.as_slice(), [.., enter, params]
            if enter.kind() == EventKind::Enter && params.kind() == EventKind::Params && enter.statement == statement)
    }

    /// Push one event. Constant; one step.
    fn log(&mut self, kind: EventKind, payload: u32, statement: NodeId) {
        self.steps += 1;
        self.events.push(Event::new(kind, payload, statement));
    }

    /// `var` joins the innermost open run unless it is in it. Constant.
    fn join(&mut self, var: VarId) {
        if !test(&self.member, var) {
            set(&mut self.member, var);
            self.seen.push(var);
        }
    }

    /// Log `Binder(var)` for the loop or `try` statement `statement`
    /// (naming.rs `stmt`, `StatementChild::Binder`: before the body). Cost:
    /// as `declare`.
    pub(crate) fn binder(&mut self, var: VarId, statement: NodeId) {
        self.log(EventKind::Binder, var.0, statement);
        if !self.open.is_empty() {
            set(&mut self.bound, var);
            self.join(var);
        }
    }

    /// Record one reference to `var` where the lowering builds it: `var`
    /// joins the open scope's run of `seen` the first time (naming.rs
    /// `analyze_expr`, `ExprKind::Var`). No event. Cost: one bit test, and
    /// one push the first time; one step.
    pub(crate) fn reference(&mut self, var: VarId) {
        self.steps += 1;
        if !self.open.is_empty() {
            self.join(var);
        }
    }

    /// Open the scope of `function` inside `statement`: log `Enter` and
    /// `Params`, mark the parameters bound (naming.rs `function`: `reserve`,
    /// `enter`, then the parameters). Returns the scope's row. The
    /// reservation list is not known yet: it is the free-variable run
    /// `leave` writes, read by the replay through the row. Cost: five
    /// pushes (the row, two events, the open scope, its mark) and one bit
    /// write per parameter; two steps.
    pub(crate) fn enter(&mut self, function: FuncId, statement: NodeId, vars: &VarTable) -> u32 {
        let row = u32::try_from(self.scopes.len()).expect("naming scope capacity");
        self.scopes.push(ScopeRow { function, free_start: 0, free_len: 0 });
        self.log(EventKind::Enter, row, statement);
        self.log(EventKind::Params, function.0, statement);
        self.open.push(row);
        self.marks.push(u32::try_from(self.seen.len()).expect("naming run capacity"));
        for param in vars.parameters(function) {
            set(&mut self.bound, param);
        }
        row
    }

    /// Close the innermost open scope: its free variables are the
    /// variables of its run of `seen` it does not bind, sorted by `order`
    /// then name (naming.rs `analyze_fun`, `sorted`); they are written to
    /// `free`, the membership and bound bits of the run are cleared through
    /// the run, and each free variable is recorded as a reference of the
    /// enclosing scope (naming.rs `analyze_expr`, `ExprKind::Fun`:
    /// `used.extend(free[f])`). Logs `Leave`. Cost: one step per variable
    /// of the run, plus the sort of the free variables (n log n
    /// comparisons); nothing is allocated once the vectors have their
    /// capacity.
    pub(crate) fn leave(&mut self, vars: &VarTable) {
        let row = self.open.pop().expect("an open function scope");
        let mark = self.marks.pop().expect("an open function run") as usize;
        self.log(EventKind::Leave, row, Self::NO_STATEMENT);
        let start = self.free.len();
        for index in mark..self.seen.len() {
            let var = self.seen[index];
            self.steps += 1;
            clear(&mut self.member, var);
            if test(&self.bound, var) {
                clear(&mut self.bound, var);
            } else {
                self.free.push(var);
            }
        }
        self.seen.truncate(mark);
        let free = &mut self.free[start..];
        free.sort_unstable_by(|&a, &b| vars.order(a).cmp(&vars.order(b)).then_with(|| vars.name(a).cmp(&vars.name(b))));
        let scope = &mut self.scopes[row as usize];
        scope.free_start = u32::try_from(start).expect("free-variable capacity");
        scope.free_len = u32::try_from(self.free.len() - start).expect("free-variable capacity");
        // naming.rs `analyze_expr`, `ExprKind::Fun`: the enclosing scope
        // uses what the function uses.
        if !self.open.is_empty() {
            for index in start..self.free.len() {
                let var = self.free[index];
                self.join(var);
            }
        }
    }

    /// The free variables of a closed scope. Constant.
    pub(crate) fn free_variables(&self, scope: u32) -> &[VarId] {
        let row = self.scopes[scope as usize];
        &self.free[row.free_start as usize..(row.free_start + row.free_len) as usize]
    }
}

/// Bit `var` of a dense bit set. Constant.
fn test(bits: &[u64], var: VarId) -> bool {
    bits[var.index() / 64] & 1 << (var.index() % 64) != 0
}
fn set(bits: &mut [u64], var: VarId) {
    bits[var.index() / 64] |= 1 << (var.index() % 64);
}
fn clear(bits: &mut [u64], var: VarId) {
    bits[var.index() / 64] &= !(1 << (var.index() % 64));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::{Bir, VarSpan};
    use crate::emit::{ProgramNames, ReplayTables, replay};
    use crate::ident::{Ident, IdentFlags};
    use crate::name::Name;

    #[test]
    fn event_sizes() {
        assert_eq!(std::mem::size_of::<EventKind>(), 1);
        assert_eq!(std::mem::size_of::<Event>(), 8);
        assert_eq!(std::mem::size_of::<ScopeRow>(), 12);
        let event = Event::new(EventKind::Binder, 7, NodeId(9));
        assert_eq!((event.kind(), event.payload(), event.statement), (EventKind::Binder, 7, NodeId(9)));
    }

    /// Variables named `names`, with order and stamp `index + 1`.
    fn unit(names: &[&str]) -> (Bir, Vec<Ident>) {
        let mut b = Bir::default();
        let mut idents = Vec::new();
        for (index, name) in names.iter().enumerate() {
            b.new_var_id(Name::new(name), index as u32 + 1);
            idents.push(Ident::new(*name, index as i32 + 1, IdentFlags::NONE));
        }
        (b, idents)
    }
    fn function(b: &mut Bir, start: u32, len: u32) -> FuncId {
        b.function_header(VarSpan { start, len }, Default::default(), crate::lambda::LamLoc::NONE)
    }
    fn printed(log: &Log, b: &Bir, idents: &[Ident], live: impl Fn(NodeId) -> bool) -> Vec<Option<String>> {
        let mut names = vec![None; idents.len()];
        let mut tables = ReplayTables::default();
        replay(&mut tables, log, b.vars(), idents, &ProgramNames::default(), live, &mut names).unwrap();
        names.into_iter().map(|name| name.map(|name| name.to_string())).collect()
    }
    const S: NodeId = NodeId(0);

    #[test]
    fn a_local_takes_the_name_of_an_outer_variable_the_function_does_not_capture() {
        // Section 2, first hard example:
        // `let y = ext(2); let k = a => { let y = ext(a); y + 1 };
        //  let k2 = a => { let y = ext(a) + y; y + 1 }`.
        let (mut b, idents) = unit(&["y", "k", "a", "y", "k2", "a", "y"]);
        let (k, k2) = (function(&mut b, 2, 1), function(&mut b, 5, 1));
        let mut log = Log::new(7);
        log.declare(VarId(0), S);
        log.enter(k, S, b.vars());
        log.declare(VarId(1), S);
        log.declare(VarId(3), S);
        log.reference(VarId(2));
        log.reference(VarId(3));
        log.leave(b.vars());
        log.enter(k2, S, b.vars());
        log.declare(VarId(4), S);
        log.declare(VarId(6), S);
        log.reference(VarId(5));
        log.reference(VarId(0));
        log.reference(VarId(6));
        log.leave(b.vars());
        assert_eq!(log.free_variables(0), &[]);
        assert_eq!(log.free_variables(1), &[VarId(0)]);
        let names = printed(&log, &b, &idents, |_| true);
        let name = |var: usize| names[var].as_deref();
        assert_eq!((name(0), name(3), name(6)), (Some("y"), Some("y"), Some("y$1")));
        assert_eq!((name(2), name(5)), (Some("a"), Some("a")));
    }

    #[test]
    fn a_new_log_has_two_bits_per_variable_and_no_open_function() {
        let log = Log::new(65);
        assert_eq!((log.member.len(), log.bound.len()), (2, 2));
        assert!(log.open.is_empty() && log.seen.is_empty() && log.marks.is_empty());
        assert!(log.events.is_empty() && log.scopes.is_empty() && log.free.is_empty());
    }

    #[test]
    fn a_loop_variable_is_named_before_the_declarations_of_its_body() {
        // `for i ... { let i = ... }`: the loop variable is `i`, the
        // declaration in the body `i$1` (loops continue their scope).
        let (b, idents) = unit(&["i", "i"]);
        let mut log = Log::new(2);
        log.binder(VarId(1), S);
        log.declare(VarId(0), S);
        let names = printed(&log, &b, &idents, |_| true);
        assert_eq!(names, vec![Some("i$1".to_string()), Some("i".to_string())]);
    }

    #[test]
    fn a_removed_declaration_takes_its_event_with_it() {
        // Section 2, second hard example: `let x = ...` removed, then
        // another `x`: the survivor prints as `x`.
        let (b, idents) = unit(&["x", "x"]);
        let mut log = Log::new(2);
        log.declare(VarId(0), NodeId(1));
        log.declare(VarId(1), NodeId(2));
        let names = printed(&log, &b, &idents, |statement| statement != NodeId(1));
        assert_eq!(names, vec![None, Some("x".to_string())]);
        let names = printed(&log, &b, &idents, |_| true);
        assert_eq!(names, vec![Some("x".to_string()), Some("x$1".to_string())]);
    }

    #[test]
    fn two_variables_first_named_by_one_reservation_are_named_in_order() {
        // Section 2, third hard example: `v` (order 2) and `v` (order 1)
        // are both first named by the reservation of `f`, which reads the
        // later-created one first: the lower order gets `v`.
        let (mut b, idents) = unit(&["v", "v", "f"]);
        let f = function(&mut b, 0, 0);
        let mut log = Log::new(3);
        log.enter(f, S, b.vars());
        log.declare(VarId(2), S);
        log.reference(VarId(1));
        log.reference(VarId(0));
        log.leave(b.vars());
        log.declare(VarId(0), S);
        log.declare(VarId(1), S);
        assert_eq!(log.free_variables(0), &[VarId(0), VarId(1)]);
        let names = printed(&log, &b, &idents, |_| true);
        assert_eq!(names, vec![Some("v".to_string()), Some("v$1".to_string()), Some("f".to_string())]);
    }

    #[test]
    fn ten_thousand_declarations_are_logged_and_replayed_in_one_step_each() {
        let names: Vec<String> = (0..10_000).map(|index| format!("v{index}")).collect();
        let names: Vec<&str> = names.iter().map(String::as_str).collect();
        let (b, idents) = unit(&names);
        let mut log = Log::new(10_000);
        for var in 0..10_000 {
            log.declare(VarId(var), S);
        }
        assert_eq!(log.steps, 10_000);
        let mut table = vec![None; 10_000];
        let mut tables = ReplayTables::default();
        let steps = replay(&mut tables, &log, b.vars(), &idents, &ProgramNames::default(), |_| true, &mut table).unwrap();
        assert_eq!(steps, 10_000);
        assert!(table.iter().all(Option::is_some));
        // Warm tables: a second replay of the same log allocates nothing.
        let allocations = allocation_counter::measure(|| {
            replay(&mut tables, &log, b.vars(), &idents, &ProgramNames::default(), |_| true, &mut table).unwrap();
        });
        assert_eq!(allocations.count_total, 0, "{allocations:?}");
    }

    #[test]
    fn ten_thousand_nested_functions_cost_a_constant_number_of_steps_each() {
        // `f0 = () => { let f1 = () => { ... x ... } }`: every function
        // declares the next and the innermost reads the outermost `x`, so
        // `x` is free in every function: one variable handed up per close.
        let mut names = vec!["x".to_string()];
        names.extend((0..10_000).map(|index| format!("f{index}")));
        let names: Vec<&str> = names.iter().map(String::as_str).collect();
        let (mut b, idents) = unit(&names);
        let mut log = Log::new(10_001);
        log.declare(VarId(0), S);
        for var in 1..=10_000 {
            let f = function(&mut b, 0, 0);
            log.enter(f, S, b.vars());
            log.declare(VarId(var), S);
        }
        log.reference(VarId(0));
        let warm = (log.events.capacity(), log.free.capacity());
        let allocations = allocation_counter::measure(|| {
            for _ in 0..10_000 {
                log.leave(b.vars());
            }
        });
        // Enter and Params, the declaration, the close and one free
        // variable per function; the first declaration and the reference.
        assert_eq!(log.steps, 2 + 10_000 * 5);
        assert_eq!(log.free.len(), 10_000);
        if warm.0 >= log.events.len() && warm.1 >= log.free.len() {
            assert_eq!(allocations.count_total, 0, "{allocations:?}");
        }
        let mut table = vec![None; 10_001];
        let mut tables = ReplayTables::default();
        let steps = replay(&mut tables, &log, b.vars(), &idents, &ProgramNames::default(), |_| true, &mut table).unwrap();
        // One step per event and one per reserved free variable.
        assert_eq!(steps, log.events.len() + 10_000);
        assert_eq!(table[0].map(|name| name.to_string()).as_deref(), Some("x"));
    }

    #[test]
    #[ignore = "T5 redesign: free variables of a function nested in a function"]
    fn a_function_nested_in_a_function_captures_a_local_of_the_outer_one() {
        // `let f = p => { let v = ext(p); let g = () => { let v' = ext(v); ext(v') }; g }`:
        // `v` is free in `g` (naming.rs `analyze_fun`), so `g`'s scope
        // inherits its group and the inner declaration is `v$1`. With one
        // membership bit per variable the bit `f` set hides the reference
        // (THREE_TREES 11.4, "T5 as built: part B", finding 1).
        let (mut b, idents) = unit(&["f", "p", "v", "g", "v"]);
        let f = function(&mut b, 1, 1);
        let g = function(&mut b, 0, 0);
        let mut log = Log::new(5);
        log.enter(f, S, b.vars());
        log.declare(VarId(0), S);
        log.declare(VarId(2), NodeId(1));
        log.reference(VarId(1));
        log.enter(g, NodeId(2), b.vars());
        log.declare(VarId(3), NodeId(2));
        log.reference(VarId(2));
        log.declare(VarId(4), NodeId(3));
        log.reference(VarId(4));
        log.leave(b.vars());
        log.leave(b.vars());
        assert_eq!(log.free_variables(1), &[VarId(2)]);
        let names = printed(&log, &b, &idents, |_| true);
        assert_eq!((names[2].as_deref(), names[4].as_deref()), (Some("v"), Some("v$1")));
    }
}
