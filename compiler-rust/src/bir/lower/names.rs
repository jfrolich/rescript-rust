//! The naming log (THREE_TREES section 2 and 11.4, "T5 part B as
//! redesigned"): what the lowering records so that printed names are
//! assigned once, when the unit's root exists, without reading an
//! expression. The rule is the header of `emit/naming.rs` (legacy
//! `JsPrinter`, compiler/ext/ext_pp_scope.ml: add_ident, merge, sub_scope);
//! that pass stays the oracle (`emit::naming::compare_with_pass`).
//!
//! Three things are recorded, each where the lowering already is:
//!
//! - per function literal one `ScopeRow`: its free variables and imports
//!   (final at the close, in `Ident`'s order) and two printer facts (the eta
//!   form, a method's `this` read). Written by `close`, after the `JFun`
//!   node exists, so the header is the printed one;
//! - per variable its home: the row of the function whose scope was the
//!   innermost open one when the variable's binder was written (`Log::bind`,
//!   from `Bir::bind`), or the row that closed with it as a parameter;
//! - nothing per reference: the references of a scope are the sites the
//!   arena recorded while the scope was open (`scope::Scope::sites`), read
//!   once, at the close of the innermost scope that was open.
//!
//! A naming event is not stored. `Declare`, `Binder` and the cached bound of
//! a range loop are read from the statement when `replay` reaches it;
//! `Enter`, `Params` and `Leave` are a scope row. So a statement that is
//! moved, copied into another list or dropped needs no bookkeeping: the
//! replay reads the lists that exist at the end.
//!
//! The lowering calls `open`, `close` and `adopt`, and `replay` when the
//! unit is complete; check mode compares the names with the pass. The
//! names are not printed yet.
use crate::bir::{Bir, FuncId, ImportId, NodeId, Op, VarId};
use crate::emit::{Printed, Subject, Tables};
use crate::name::Name;

/// A row of `Log::rows`. Row 0 is the program.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ScopeId(pub(crate) u32);
impl ScopeId {
    pub(crate) const PROGRAM: Self = Self(0);
    /// No scope: the home of a variable without a binder.
    pub(crate) const NONE: Self = Self(u32::MAX);
}

/// One entry of a free list: a variable, or an imported module (the pass
/// counts a module reference as a use, and a function inherits the names of
/// the module's base like those of a variable's).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct FreeRef(u32);
impl FreeRef {
    const IMPORT: u32 = 1 << 31;
    /// Constant.
    pub(crate) fn var(var: VarId) -> Self {
        assert!(var.0 < Self::IMPORT, "variable capacity");
        Self(var.0)
    }
    /// Constant.
    pub(crate) fn import(import: ImportId) -> Self {
        assert!(import.0 < Self::IMPORT, "import capacity");
        Self(import.0 | Self::IMPORT)
    }
    /// Constant.
    pub(crate) fn as_var(self) -> Option<VarId> {
        (self.0 & Self::IMPORT == 0).then_some(VarId(self.0))
    }
    /// Constant.
    pub(crate) fn as_import(self) -> Option<ImportId> {
        (self.0 & Self::IMPORT != 0).then_some(ImportId(self.0 & !Self::IMPORT))
    }
}

/// One function literal: the header it prints with, its free list as a run
/// of `Log::free`, and what the printer decides from the finished function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ScopeRow {
    /// The header of the `JFun` (after a unit parameter was dropped and
    /// after the tail-call rewrite replaced the parameters). The node is
    /// `Bir::func_owners[function]`; none when the literal was released.
    pub(crate) function: FuncId,
    pub(crate) free_start: u32,
    pub(crate) free_len: u32,
    /// `CLOSED`, `ETA`, `FIRST_READ`, `COPY`.
    pub(crate) flags: u32,
}
impl ScopeRow {
    /// `close` has written the row.
    pub(crate) const CLOSED: u32 = 1;
    /// The function has the shape the printer eta-reduces
    /// (`walk::eta_target`, `eta_shape`). Unless it is a method, its binder
    /// is named before the reservation and its parameters get no name.
    /// Whether it is a method is read from the header when the replay
    /// reaches it: the lowering makes a function a method after its close
    /// (`prim.rs`, `PjsFnMethod`).
    pub(crate) const ETA: u32 = 2;
    /// The body reads the function's first parameter. Recorded for every
    /// function, because a function becomes a method after its close; the
    /// first parameter of a method is named only when it is read
    /// (naming.rs `analyze_fun`, `method_this`).
    pub(crate) const FIRST_READ: u32 = 4;
    /// The row of a copy (`Log::copied`): it shares the free run of its
    /// source. The pass has one function for both.
    pub(crate) const COPY: u32 = 8;
}

/// One open scope: its row and where its part of each stack starts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Open {
    row: u32,
    /// `Scope::sites.len()` when the scope opened.
    sites: u32,
    /// `Log::run.len()` when the scope opened.
    run: u32,
    /// `Log::children.len()` when the scope opened.
    children: u32,
}

/// The log of one unit. Lives on the arena's `Scope` beside the counts.
#[derive(Default)]
pub(crate) struct Log {
    /// Row 0 is the program; a function's row is pushed by `open`.
    pub(crate) rows: Vec<ScopeRow>,
    /// The free lists of the closed scopes, back to back.
    pub(crate) free: Vec<FreeRef>,
    /// The row of each function header plus one, zero for none. Dense by
    /// FuncId, grown by `close` and `copied`.
    of_function: Vec<u32>,
    /// The row that binds each variable. Dense by VarId.
    home: Vec<u32>,
    /// The row that last put each variable in its run. Dense by VarId.
    seen: Vec<u32>,
    /// The same for imports. Dense by ImportId, grown on demand.
    seen_import: Vec<u32>,
    /// The open scopes, innermost last. The program is never on it.
    open: Vec<Open>,
    /// What the open scopes reference, innermost run last: imports as they
    /// are referenced, free entries handed up by closed children.
    run: Vec<FreeRef>,
    /// The site ranges `[start, end)` of the closed direct children of the
    /// open scopes, innermost run last.
    children: Vec<[u32; 2]>,
    /// The nodes `adopt` has still to read. Empty between calls.
    pending: Vec<NodeId>,
    /// Nodes `adopt` read: what the one walk over an expression costs.
    pub(crate) adopted_nodes: usize,
    /// Sites read, run entries read, children skipped, comparisons of the
    /// sort, rows copied, nodes adopted and free entries taken over by
    /// `adopt`.
    pub(crate) steps: usize,
}

impl Log {
    /// A log for a unit of `variables` variables with the program row and
    /// no open function. Cost: two words per variable, allocated once.
    pub(crate) fn new(variables: usize) -> Self {
        let program = ScopeRow { function: FuncId(u32::MAX), free_start: 0, free_len: 0, flags: 0 };
        Self {
            rows: vec![program],
            home: vec![ScopeId::NONE.0; variables],
            seen: vec![ScopeId::NONE.0; variables],
            ..Self::default()
        }
    }

    /// A variable was created (`Bir::new_var_id`, beside `Scope::push`):
    /// its home is `ScopeId::NONE`. Cost: two pushes; no step.
    pub(crate) fn variable(&mut self) {
        self.home.push(ScopeId::NONE.0);
        self.seen.push(ScopeId::NONE.0);
    }

    /// The binder of `var` was written (`Bir::bind`, for every binder but a
    /// function's parameters: a declaration, a rest field, a loop variable,
    /// a catch variable): its home is the innermost open scope, the program
    /// when none is open. A variable bound again (a copy made while another
    /// scope is open rebinds nothing: a copy has variables of its own) keeps
    /// the last write.
    ///
    /// `Bir::copy_subtree` calls it for the parameters of a function literal
    /// it copies too: no scope opens or closes for a copy, so the innermost
    /// open scope reads the copy's sites as its own, and every binder of
    /// the copy, a parameter included, has to be at home there or the scope
    /// would list it as free. Cost: one write; no step.
    pub(crate) fn bind(&mut self, var: VarId) {
        self.home[var.index()] = self.open.last().map_or(ScopeId::PROGRAM.0, |open| open.row);
    }

    /// `Bir::copy_subtree` copied the function literal with header `source`
    /// to one with header `copy` (`bir::j::logic::copy_j`): a row for the
    /// copy that shares the source's free run and flags, with `COPY`. The
    /// copy's own binders print as their origins (`vars.j_origin`), so the
    /// shared list names the same identifiers; their home is the scope the
    /// copy was made in (`Log::bind`). Nothing when `source` has no
    /// closed row (a function of the source arena). Cost: one push and one
    /// write; one step.
    pub(crate) fn copied(&mut self, source: FuncId, copy: FuncId) -> Option<ScopeId> {
        let source = self.scope(source)?;
        let row = self.rows[source.0 as usize];
        if row.flags & ScopeRow::CLOSED == 0 {
            return None;
        }
        let scope = ScopeId(index(self.rows.len()));
        self.rows.push(ScopeRow { function: copy, flags: row.flags | ScopeRow::COPY, ..row });
        self.set_scope(copy, scope);
        self.steps += 1;
        Some(scope)
    }

    /// Record `scope` as the row of `function`. Amortized O(1).
    fn set_scope(&mut self, function: FuncId, scope: ScopeId) {
        if self.of_function.len() <= function.index() {
            self.of_function.resize(function.index() + 1, 0);
        }
        self.of_function[function.index()] = scope.0 + 1;
    }

    /// The row of the function with header `function`. Constant.
    pub(crate) fn scope(&self, function: FuncId) -> Option<ScopeId> {
        match self.of_function.get(function.index()) {
            Some(&row) if row != 0 => Some(ScopeId(row - 1)),
            _ => None,
        }
    }

    /// The home of `var`. Constant.
    pub(crate) fn home(&self, var: VarId) -> ScopeId {
        ScopeId(self.home[var.index()])
    }

    /// The free list of a closed scope: sorted by `Ident`'s order (stamp,
    /// then name; an import by its module identifier), one entry per
    /// identifier.
    /// Constant.
    pub(crate) fn free(&self, scope: ScopeId) -> &[FreeRef] {
        let row = self.rows[scope.0 as usize];
        &self.free[row.free_start as usize..(row.free_start + row.free_len) as usize]
    }

    /// Put `entry` in the run of the open scope `row` unless that scope put
    /// it there before. Amortized O(1); no step.
    fn join(&mut self, row: u32, entry: FreeRef) {
        let seen = match (entry.as_var(), entry.as_import()) {
            (Some(var), _) => &mut self.seen[var.index()],
            (None, Some(import)) => {
                if self.seen_import.len() <= import.index() {
                    self.seen_import.resize(import.index() + 1, ScopeId::NONE.0);
                }
                &mut self.seen_import[import.index()]
            }
            (None, None) => unreachable!("a free entry is a variable or an import"),
        };
        if *seen != row {
            *seen = row;
            self.run.push(entry);
        }
    }

    /// `close` on the log taken out of `bir` (see `close`).
    fn close(&mut self, bir: &Bir, idents: &[crate::ident::Ident], function: FuncId) -> ScopeId {
        let open = self.open.pop().expect("a function scope is open");
        let row = open.row;
        // 1. The parameters are bound here.
        let header = bir.function(function);
        for i in 0..header.params.len() {
            self.home[bir.function_parameter(function, i).index()] = row;
        }
        // 2. This scope's own sites: those outside its closed children.
        let sites = &bir.js_scope.as_ref().expect("lowering scope").sites;
        let end = index(sites.len());
        let mut at = open.sites;
        let children = open.children as usize;
        let mut child = children;
        while let Some(&[start, stop]) = self.children.get(child) {
            self.steps += 1;
            self.read_sites(bir, row, at, start);
            at = stop;
            child += 1;
        }
        self.read_sites(bir, row, at, end);
        // 3. The free entries of the run, compacted in place.
        let first = (!header.params.is_empty()).then(|| FreeRef::var(bir.function_parameter(function, 0)));
        let mut flags = ScopeRow::CLOSED;
        let start = open.run as usize;
        let mut kept = start;
        for i in start..self.run.len() {
            self.steps += 1;
            let entry = self.run[i];
            if Some(entry) == first {
                flags |= ScopeRow::FIRST_READ;
            }
            if entry.as_var().is_none_or(|var| self.home(var) != ScopeId(row)) {
                self.run[kept] = entry;
                kept += 1;
            }
        }
        self.run.truncate(kept);
        // 4. Sorted by `Ident`'s order, written without duplicates.
        let mut comparisons = 0;
        self.run[start..].sort_unstable_by(|&a, &b| {
            comparisons += 1;
            ident_order(bir, idents, a, b)
        });
        self.steps += comparisons;
        // Two entries of one identifier are one entry: two imports of one
        // module identifier (a module the source reads and the runtime
        // module of that name), or two variables the lowering made for one
        // JavaScript name. The pass keeps a set of identifiers.
        let free_start = index(self.free.len());
        let mut last = None;
        for &entry in &self.run[start..kept] {
            let ident = ident_of(bir, idents, entry);
            let repeated = index(self.free.len()) != free_start
                && match (ident, last) {
                    (Some(ident), Some(last)) => ident == last,
                    _ => self.free.last() == Some(&entry),
                };
            if !repeated {
                self.free.push(entry);
            }
            last = ident;
        }
        self.run.truncate(start);
        let free_len = index(self.free.len()) - free_start;
        let node = bir.func_owners[function.index()].expect("close after the function literal is built");
        if eta_shape(bir, node) {
            flags |= ScopeRow::ETA;
        }
        self.rows[row as usize] = ScopeRow { function, free_start, free_len, flags };
        let scope = ScopeId(row);
        self.set_scope(function, scope);
        // 5. Handed up to the enclosing open scope.
        self.children.truncate(children);
        if let Some(parent) = self.open.last().map(|open| open.row) {
            for i in free_start..free_start + free_len {
                self.steps += 1;
                self.join(parent, self.free[i as usize]);
            }
            self.children.push([open.sites, end]);
        }
        scope
    }

    /// Step 2 of `close` over the sites `[from, to)`: one step each.
    fn read_sites(&mut self, bir: &Bir, row: u32, from: u32, to: u32) {
        let sites = &bir.js_scope.as_ref().expect("lowering scope").sites;
        for site in &sites[from as usize..to as usize] {
            self.steps += 1;
            if site.node == NodeId(u32::MAX) {
                continue;
            }
            let entry = match bir.view(site.node) {
                crate::bir::View::Var { var } => FreeRef::var(var),
                crate::bir::View::JQualified { module, .. } => FreeRef::import(module),
                _ => unreachable!("a site is a reference"),
            };
            self.join(row, entry);
        }
    }

    /// `adopt` on the log taken out of `bir` (see `adopt`).
    fn adopt(&mut self, bir: &Bir, node: NodeId) {
        let row = self.open.last().expect("adopt inside an open function scope").row;
        debug_assert!(self.pending.is_empty());
        self.pending.push(node);
        while let Some(node) = self.pending.pop() {
            self.steps += 1;
            self.adopted_nodes += 1;
            match bir.view(node) {
                crate::bir::View::Var { var } => self.join(row, FreeRef::var(var)),
                crate::bir::View::JQualified { module, .. } => self.join(row, FreeRef::import(module)),
                crate::bir::View::JFun { header, .. } => {
                    let scope = self.scope(header).expect("an adopted function literal is closed");
                    let literal = self.rows[scope.0 as usize];
                    assert!(literal.flags & ScopeRow::CLOSED != 0, "an adopted function literal is closed");
                    for i in literal.free_start..literal.free_start + literal.free_len {
                        self.steps += 1;
                        self.join(row, self.free[i as usize]);
                    }
                }
                view => view.children_into(&mut self.pending),
            }
        }
    }
}

/// `Ident`'s order of two free entries (`Ident::cmp`: stamp, then name,
/// then flags; a variable by the identifier of its origin, an import by its
/// module identifier), then the entries' own order, so that equal entries
/// are adjacent. It is the order the pass sorts a free list by (naming.rs
/// `sorted`), read from the same identifiers: a variable's `order` is not
/// its stamp for a hidden identifier (stamp -1) or for a variable the
/// lowering made for a JavaScript name (stamp 0). Constant.
fn ident_order(bir: &Bir, idents: &[crate::ident::Ident], a: FreeRef, b: FreeRef) -> std::cmp::Ordering {
    if a == b {
        return std::cmp::Ordering::Equal;
    }
    // A variable without an identifier is never reserved
    // (`Replay::subject`); it sorts before the others.
    ident_of(bir, idents, a).cmp(&ident_of(bir, idents, b)).then(a.cmp(&b))
}

/// The identifier a free entry prints as: a variable's through its origin,
/// an import's module identifier. Constant.
fn ident_of(bir: &Bir, idents: &[crate::ident::Ident], entry: FreeRef) -> Option<crate::ident::Ident> {
    match (entry.as_var(), entry.as_import()) {
        (Some(var), _) => idents.get(bir.vars.j_origin[var.index()].index()).copied(),
        (None, Some(import)) => Some(bir.pools.j_modules[import.index()].id),
        (None, None) => unreachable!("a free entry is a variable or an import"),
    }
}

/// A `u32` index. Constant.
fn index(len: usize) -> u32 {
    u32::try_from(len).expect("naming log capacity")
}

/// A function's scope opens: call it where the lowering starts the body of
/// a function literal (`State::enter`, `View::Fun`), and where it starts
/// building a function of its own (`call.rs`, `ffi_args.rs`, `import.rs`),
/// before the first node of the body is built. Pushes the scope's row and
/// its entry on the open stack. Cost: two pushes; no step.
pub(crate) fn open(bir: &mut Bir) -> ScopeId {
    let scope = bir.js_scope.as_mut().expect("lowering scope");
    let sites = index(scope.sites.len());
    let log = &mut scope.names;
    let row = index(log.rows.len());
    log.rows.push(ScopeRow { function: FuncId(u32::MAX), free_start: 0, free_len: 0, flags: 0 });
    log.open.push(Open { row, sites, run: index(log.run.len()), children: index(log.children.len()) });
    ScopeId(row)
}

/// The innermost open scope closes: call it once the `JFun` with header
/// `function` is built (after `loop_function_body` and after the header
/// without the unit parameter was allocated), so that the function's
/// parameters, body and node are the printed ones.
///
/// 1. The parameters of `function` get this row as their home.
/// 2. The sites recorded since the scope opened, outside the ranges of its
///    closed direct children, are read once each: a live site (its node is
///    not released) whose variable this scope did not see yet joins the run.
/// 3. Each entry of the run whose home is not this row is free. The first
///    parameter in the run sets `FIRST_READ`.
/// 4. The free entries are sorted by `Ident`'s order and written, one per
///    identifier, as the row's run of `Log::free`; `ETA` is `eta_shape` of
///    the node.
/// 5. Each free entry joins the enclosing open scope's run (naming.rs
///    `analyze_expr`, `ExprKind::Fun`: `used.extend(free[f])`), and this
///    scope's site range joins the enclosing scope's children.
///
/// Cost: one step per site of step 2, one per closed direct child, one per
/// entry of the run, one per comparison of the sort, one per free entry
/// handed up; nothing is allocated once the vectors have their capacity. A
/// site is read at one close only, so the sites cost one step each over the
/// whole unit, whatever the nesting.
pub(crate) fn close(bir: &mut Bir, idents: &[crate::ident::Ident], function: FuncId) -> ScopeId {
    let mut log = std::mem::take(&mut bir.js_scope.as_mut().expect("lowering scope").names);
    let scope = log.close(bir, idents, function);
    bir.js_scope.as_mut().expect("lowering scope").names = log;
    scope
}

/// An expression that was built before the innermost open scope opened
/// moves into that scope's function: call it once per such expression,
/// between `open` and `close` (the eta-expansion of a partial application,
/// `apply_with_arity`: the callee and each remaining argument; the dispatch
/// function of an external's argument, `external_dispatch`: the argument).
/// Its references were recorded as sites before the scope opened, between
/// the sites of statements that stay outside, so no site range describes
/// them (THREE_TREES 11.4, "T5 part B as redesigned", G10).
///
/// Reads the subtree of `node` once: a `Var` joins the open scope's run
/// unless that scope saw the variable; a `JQualified` joins it as an import
/// in the same way; a function literal is not entered: the free entries of
/// its closed row join the run (a literal without a closed row is a bug of
/// the caller: asserts). The enclosing scope needs nothing: it read the
/// moved references as its own sites, and `close` hands this scope's free
/// entries up as for any function.
///
/// This is the one place where an expression is read for a reference.
/// Cost: one step per node of the subtree outside function literals, one
/// per function literal and one per free entry of each; `adopted_nodes`
/// grows by the nodes read. Nothing is allocated once `pending` has its
/// capacity. Asserts that a function scope is open.
pub(crate) fn adopt(bir: &mut Bir, node: NodeId) {
    let mut log = std::mem::take(&mut bir.js_scope.as_mut().expect("lowering scope").names);
    log.adopt(bir, node);
    bir.js_scope.as_mut().expect("lowering scope").names = log;
}

/// Whether the printer eta-reduces the function literal `function`
/// (`emit::walk::eta_target`, on the finished node): not a method, not
/// `async`, no directive, and the body is one `return callee(arguments)`
/// with a variable or module member as callee and exactly the parameters as
/// arguments, in order. Cost: one step per parameter; the body is not read
/// beyond its one statement.
pub(crate) fn eta_shape(bir: &Bir, function: NodeId) -> bool {
    use crate::bir::View;
    use crate::js_ir::{CallArity, CallKind};
    let View::JFun { body, header } = bir.view(function) else { return false };
    let attributes = bir.function_attributes(header);
    if bir.function(header).flags & crate::bir::FuncHeader::METHOD != 0 || attributes.async_ || attributes.directive.is_some() {
        return false;
    }
    let View::SBlock { statements: &[statement] } = bir.view(body) else { return false };
    let View::SReturn { value } = bir.view(statement) else { return false };
    let View::JCall { callee, args, info } = bir.view(value) else { return false };
    let callee = match bir.view(callee) {
        View::Var { var } => Some(var),
        View::JQualified { .. } => None,
        _ => return false,
    };
    let params = bir.function(header).params.len();
    if args.len() != params {
        return false;
    }
    for (i, &arg) in args.iter().enumerate() {
        let param = bir.function_parameter(header, i);
        if !matches!(bir.view(arg), View::Var { var } if var == param) || callee == Some(param) {
            return false;
        }
    }
    let crate::bir::JsPayload::Call(info) = bir.javascript(info) else { return false };
    matches!(info.kind, CallKind::MlCall | CallKind::BuiltinRuntime) && info.arity == CallArity::Full
}

/// What the program scope names besides its statements, in the pass's order
/// (`Names::collect`): the imported modules that are neither dynamic nor
/// unresolved, then the reservations of export coercion, then the
/// statements, then the exports. `raw` holds the spellings the pass skips
/// when it picks a suffix (`Names::raw`: the name of every variable that is
/// a JavaScript name, `js_ir::arena::is_raw_js_name`, and occurs).
pub(crate) struct Program<'a> {
    pub(crate) imports: &'a [ImportId],
    pub(crate) reservations: &'a [Subject],
    pub(crate) exports: &'a [VarId],
    pub(crate) raw: &'a [Name],
}

/// One level of the replay's walk over statement lists.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Frame {
    /// The statement whose children are being read.
    statement: NodeId,
    /// The next child list or literal to read.
    at: u32,
    /// The scope row to leave when the frame is done, or `ScopeId::NONE`.
    leave: u32,
}

/// Storage the replay reuses between units.
#[derive(Default)]
pub(crate) struct Scratch {
    /// Dense by NodeId, sized to the arena at each replay. For a statement:
    /// the first of its function literals (a row) plus one. For an
    /// expression on the way from a literal to its statement: the statement
    /// plus one.
    marks: Vec<u32>,
    /// The next literal of the same statement, plus one. Dense by row.
    next: Vec<u32>,
    frames: Vec<Frame>,
    /// The reservation of the function being entered.
    reservation: Vec<Subject>,
    /// The spelling of a cached bound's base, reused.
    spelling: String,
}

/// What one replay did.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize)]
pub(crate) struct Replayed {
    /// Statements read, one step each.
    pub(crate) statements: usize,
    /// Scope rows read, one step each (a released literal included).
    pub(crate) scopes: usize,
    /// Free entries and binders reserved, one step each.
    pub(crate) reserved: usize,
    /// Ancestors read on the way from a literal to its statement.
    pub(crate) ancestors: usize,
    /// Reservations that named a variable for the first time in a statement
    /// with more than one function literal: the order of the literals then
    /// decides names, and the replay reads them in the order they closed.
    pub(crate) ambiguous_orders: usize,
    /// Variables with a live reference, a stamp and no name at the end: a
    /// use the pass would have named.
    pub(crate) unnamed_references: usize,
}
impl Replayed {
    /// All steps. Constant.
    pub(crate) fn steps(&self) -> usize {
        self.statements + self.scopes + self.reserved + self.ancestors
    }
}

/// Assign the printed names of the unit whose root block is `root`
/// (`State::finish`, after `globals::decide`; the log is the arena's).
///
/// Prelude: each closed row whose literal is live is attached to the
/// statement its literal stands in, by reading the literal's ancestors up
/// to the first statement or marked expression (rows last to first, each
/// pushed at the front of its statement's chain, so a chain is in closing
/// order).
///
/// Then the program, in the pass's order: the imports (`Tables::add_module`),
/// the reservations, the statements of `root`, the exports. A statement, by
/// its kind (naming.rs `stmt`): the binders it names (a declaration's rest
/// fields, then its variable; a loop variable; `Tables::synthetic` for the
/// cached bound of a range loop whose bound is neither a number nor a
/// reference), then its function literals, then its child lists in print
/// order, the catch variable of a `try` between its body and its handler.
/// A function literal (naming.rs `function`): the reservation is its free
/// list with the binder of its declaration merged in, in `Ident`'s order;
/// for `ETA` the binder is named before the reservation; `Tables::reserve`
/// each, the binder named, `Tables::enter`; unless `ETA`, the parameters
/// (not the first one of a method without `FIRST_READ`) and the body's list;
/// `Tables::leave`.
///
/// No expression is read: a function literal is reached through its row.
/// Cost: one step per statement of the final lists, one per row, one per
/// reserved entry, one per ancestor between a literal and its statement (a
/// node is read at most twice), plus the cost of each `Tables` call. `marks`
/// is cleared once per unit (four bytes a node). Nothing is allocated once
/// `scratch`, `tables` and `printed` have held a unit of this size.
pub(crate) fn replay(
    bir: &Bir,
    root: NodeId,
    idents: &[crate::ident::Ident],
    program: &Program<'_>,
    tables: &mut Tables,
    scratch: &mut Scratch,
    printed: &mut Printed,
) -> Replayed {
    let scope = bir.js_scope.as_ref().expect("lowering scope");
    let log = &scope.names;
    let variables = bir.vars.len();
    let imports = bir.pools.j_modules.len();
    tables.begin(variables + imports, program.raw);
    printed.names.clear();
    printed.names.resize(variables, None);
    printed.modules.clear();
    printed.modules.resize(imports, None);
    printed.finishes.clear();
    let mut replay = Replay { bir, idents, log, tables, scratch, printed, done: Replayed::default() };
    replay.prelude();
    for &import in program.imports {
        replay.name_import(import);
    }
    for &subject in program.reservations {
        replay.tables.reserve(subject);
        if subject.stamp != 0 && (subject.slot as usize) < variables {
            replay.printed.names[subject.slot as usize] = Some(replay.tables.add(subject));
        }
    }
    replay.statements(root);
    for &var in program.exports {
        replay.name(var);
    }
    // A use names nothing here: a variable that is referenced and has no
    // name is one the pass would have named at the use, unless it is a
    // parameter of a function the printer eta-reduces, which no side names.
    for var in 0..variables {
        let referenced = scope.uses.get(var).is_some_and(|uses| uses.remaining > 0);
        if referenced
            && replay.printed.names[var].is_none()
            && replay.subject(VarId(var as u32)).is_some_and(|s| s.stamp != 0)
            && !replay.eta_parameter(VarId(var as u32))
        {
            replay.done.unnamed_references += 1;
        }
    }
    replay.done
}

/// A frame's `at` while it reads its statement's function literals: this
/// bit and the row; without it, the index of the next child list.
const LITERAL: u32 = 1 << 31;

/// The state of one `replay`.
struct Replay<'a, 'b> {
    bir: &'a Bir,
    idents: &'a [crate::ident::Ident],
    log: &'a Log,
    tables: &'b mut Tables,
    scratch: &'b mut Scratch,
    printed: &'b mut Printed,
    done: Replayed,
}

impl Replay<'_, '_> {
    /// Attach each closed, live row to the statement its literal stands in
    /// (see `replay`). One step per row and per ancestor read; an ancestor
    /// is read once on the first walk and once when it is marked.
    fn prelude(&mut self) {
        let (bir, scratch) = (self.bir, &mut *self.scratch);
        scratch.marks.clear();
        scratch.marks.resize(bir.nodes.len(), 0);
        scratch.next.clear();
        scratch.next.resize(self.log.rows.len(), 0);
        for row in (1..self.log.rows.len()).rev() {
            self.done.scopes += 1;
            let info = self.log.rows[row];
            if info.flags & ScopeRow::CLOSED == 0 {
                continue;
            }
            let Some(literal) = bir.func_owners.get(info.function.index()).copied().flatten() else { continue };
            // The first walk: up to a statement or a marked expression.
            let mut at = bir.parents[literal.index()];
            let (stop, statement) = loop {
                let Some(node) = at else { break (None, None) };
                self.done.ancestors += 1;
                if is_statement(bir.nodes[node.index()].op()) {
                    break (Some(node), Some(node));
                }
                let mark = scratch.marks[node.index()];
                if mark != 0 {
                    break (Some(node), Some(NodeId(mark - 1)));
                }
                at = bir.parents[node.index()];
            };
            let (Some(stop), Some(statement)) = (stop, statement) else { continue };
            // The second walk marks the expressions passed on the first.
            let mut node = bir.parents[literal.index()].expect("read on the first walk");
            while node != stop {
                self.done.ancestors += 1;
                scratch.marks[node.index()] = statement.0 + 1;
                node = bir.parents[node.index()].expect("read on the first walk");
            }
            scratch.next[row] = scratch.marks[statement.index()];
            scratch.marks[statement.index()] = row as u32 + 1;
        }
    }

    /// The statements of the block `root` and everything below them, one
    /// frame per open list.
    fn statements(&mut self, root: NodeId) {
        self.scratch.frames.clear();
        self.scratch.frames.push(Frame { statement: root, at: 0, leave: ScopeId::NONE.0 });
        while let Some(&frame) = self.scratch.frames.last() {
            if frame.at & LITERAL != 0 {
                let row = frame.at & !LITERAL;
                let next = self.scratch.next[row as usize];
                self.scratch.frames.last_mut().expect("the frame read").at = if next == 0 { 0 } else { LITERAL | (next - 1) };
                self.literal(row, frame.statement);
                continue;
            }
            let Some(child) = self.child(frame.statement, frame.at) else {
                self.scratch.frames.pop();
                if frame.leave != ScopeId::NONE.0 {
                    self.tables.leave();
                }
                continue;
            };
            self.scratch.frames.last_mut().expect("the frame read").at += 1;
            let in_list = self.bir.nodes[frame.statement.index()].op() == Op::SBlock;
            if in_list {
                self.done.statements += 1;
            }
            self.statement(child);
        }
    }

    /// Child list `index` of `statement` in print order, or a statement of
    /// a block; for a `try`, its catch variable is named before its handler.
    /// Constant.
    fn child(&mut self, statement: NodeId, index: u32) -> Option<NodeId> {
        use crate::bir::View;
        let i = index as usize;
        match self.bir.view(statement) {
            View::SBlock { statements } => statements.get(i).copied(),
            View::SIf { then_, else_, .. } => match i {
                0 => Some(then_),
                1 => else_,
                _ => None,
            },
            View::SWhile { body, .. } => (i == 0).then_some(body),
            View::SForRange { parts, .. }
            | View::SForRangeExisting { parts, .. }
            | View::SForOf { parts, .. }
            | View::SForAwaitOf { parts, .. } => (i == 0).then(|| parts[parts.len() - 1]),
            View::STry { parts, exception } => {
                if i == 1
                    && let Some(var) = exception
                {
                    self.name(var);
                }
                parts.get(i).copied()
            }
            View::SSwitch { actions, .. } => actions.get(i).copied(),
            _ => None,
        }
    }

    /// Reach `statement`: name its binders and open its frame, which reads
    /// its function literals, then its child lists.
    fn statement(&mut self, statement: NodeId) {
        use crate::bir::View;
        let bir = self.bir;
        match bir.view(statement) {
            View::SDecl { var, value } => {
                // A function literal as the value names the binder with its
                // reservation (`literal`).
                if !value.is_some_and(|value| self.closed_literal(value)) {
                    self.name(var);
                }
            }
            View::SRest { var, info, .. } => {
                if let crate::bir::JsPayload::Rest(fields) = bir.javascript(info) {
                    for field in bir.rest_fields(*fields) {
                        if let Some(binding) = field.binding {
                            self.name(binding);
                        }
                    }
                }
                self.name(var);
            }
            View::SForRange { var, parts, .. } => {
                self.name(var);
                self.finish(var, parts[parts.len() - 2]);
            }
            View::SForRangeExisting { variable, parts, .. } => {
                if let View::Var { var } = bir.view(variable) {
                    self.finish(var, parts[parts.len() - 2]);
                }
            }
            View::SForOf { var, .. } | View::SForAwaitOf { var, .. } => self.name(var),
            _ => {}
        }
        let first = self.scratch.marks[statement.index()];
        let at = if first == 0 { 0 } else { LITERAL | (first - 1) };
        self.scratch.frames.push(Frame { statement, at, leave: ScopeId::NONE.0 });
    }

    /// Whether `var` is a parameter of a function literal whose row has
    /// `ETA`: the printer eta-reduces it, and the pass names none of its
    /// parameters (naming.rs `function`, `FunctionForm::Eta`). A copy's
    /// parameters are read through the copy's literal. Constant.
    fn eta_parameter(&self, var: VarId) -> bool {
        let Some(binder) = self.bir.vars.binder(var) else { return false };
        if self.bir.nodes[binder.index()].op() != Op::JFun {
            return false;
        }
        let crate::bir::View::JFun { header, .. } = self.bir.view(binder) else { return false };
        self.log.scope(header).is_some_and(|scope| self.eta(self.log.rows[scope.0 as usize]))
    }

    /// Whether the printer eta-reduces the function of `row`: it had the
    /// shape at its close and is no method now (a function made a method
    /// after its close keeps `ETA`; `walk::eta_target` refuses a method).
    /// Constant.
    fn eta(&self, row: ScopeRow) -> bool {
        row.flags & ScopeRow::ETA != 0 && self.bir.function(row.function).flags & crate::bir::FuncHeader::METHOD == 0
    }

    /// Whether `node` is a function literal with a closed row.
    fn closed_literal(&self, node: NodeId) -> bool {
        use crate::bir::View;
        let View::JFun { header, .. } = self.bir.view(node) else { return false };
        self.log.scope(header).is_some_and(|scope| self.log.rows[scope.0 as usize].flags & ScopeRow::CLOSED != 0)
    }

    /// The cached bound of a range loop over `var`, when the bound `end` is
    /// neither a number nor a reference (`walk::finish_binding`).
    fn finish(&mut self, var: VarId, end: NodeId) {
        if matches!(self.bir.nodes[end.index()].op(), Op::JNumber | Op::Var | Op::JQualified) {
            return;
        }
        let Some(subject) = self.subject(var) else { return };
        let spelling = &mut self.scratch.spelling;
        spelling.clear();
        spelling.push_str(crate::js_ir::printer::convert_ident_atom(subject.name).as_str());
        spelling.push_str("_finish");
        let name = self.tables.synthetic(Name::new(spelling));
        self.printed.finishes.push(name);
    }

    /// The function literal of `row`, standing in `statement`: its
    /// reservation, its scope, its parameters and its body's frame.
    fn literal(&mut self, row: u32, statement: NodeId) {
        use crate::bir::View;
        let bir = self.bir;
        let info = self.log.rows[row as usize];
        let node = bir.func_owners[info.function.index()].expect("an attached row is live");
        let binder = match bir.view(statement) {
            View::SDecl { var, value: Some(value) } if value == node => Some(var),
            _ => None,
        };
        let eta = self.eta(info);
        if eta && let Some(binder) = binder {
            self.name(binder);
        }
        // More than one literal in the statement: the order of the
        // reservations is the closing order, not a print order.
        let first = self.scratch.marks[statement.index()] - 1;
        let several = self.scratch.next[first as usize] != 0;
        self.scratch.reservation.clear();
        let mut pending = binder.map(FreeRef::var);
        let log = self.log;
        for &entry in log.free(ScopeId(row)) {
            if let Some(own) = pending {
                match ident_order(bir, self.idents, own, entry) {
                    std::cmp::Ordering::Less => {
                        self.reserve(own, several);
                        pending = None;
                    }
                    std::cmp::Ordering::Equal => pending = None,
                    std::cmp::Ordering::Greater => {}
                }
            }
            self.reserve(entry, several);
        }
        if let Some(own) = pending {
            self.reserve(own, several);
        }
        if let Some(binder) = binder {
            self.name(binder);
        }
        self.tables.enter(&self.scratch.reservation);
        if eta {
            self.tables.leave();
            return;
        }
        let header = bir.function(info.function);
        let method = header.flags & crate::bir::FuncHeader::METHOD != 0;
        for i in 0..header.params.len() {
            if i == 0 && method && info.flags & ScopeRow::FIRST_READ == 0 {
                continue;
            }
            self.name(bir.function_parameter(info.function, i));
        }
        let View::JFun { body, .. } = bir.view(node) else { unreachable!("a row's node is a function literal") };
        self.scratch.frames.push(Frame { statement: body, at: 0, leave: row });
    }

    /// Reserve one entry of a literal's reservation and keep it for
    /// `Tables::enter`. One step.
    fn reserve(&mut self, entry: FreeRef, several: bool) {
        let subject = match (entry.as_var(), entry.as_import()) {
            (Some(var), _) => self.subject(var),
            (None, Some(import)) => Some(self.import_subject(import)),
            (None, None) => unreachable!("a free entry is a variable or an import"),
        };
        let Some(subject) = subject else { return };
        self.done.reserved += 1;
        if self.tables.reserve(subject) && several {
            self.done.ambiguous_orders += 1;
        }
        self.scratch.reservation.push(subject);
        if subject.stamp == 0 {
            return;
        }
        match (entry.as_var(), entry.as_import()) {
            (Some(var), _) => self.printed.names[var.index()] = Some(self.tables.add(subject)),
            (None, Some(import)) => self.printed.modules[import.index()] = Some(self.tables.add_module(subject)),
            (None, None) => {}
        }
    }

    /// Name the binder `var` in the current scope (`Tables::add`).
    fn name(&mut self, var: VarId) {
        if let Some(subject) = self.subject(var) {
            self.printed.names[var.index()] = Some(self.tables.add(subject));
        }
    }

    /// Name an imported module in the program (`Tables::add_module`).
    fn name_import(&mut self, import: ImportId) {
        let subject = self.import_subject(import);
        self.printed.modules[import.index()] = Some(self.tables.add_module(subject));
    }

    /// The identifier `var` prints as: its origin's. None for a variable
    /// without an identifier.
    fn subject(&self, var: VarId) -> Option<Subject> {
        let origin = self.bir.vars.j_origin[var.index()];
        let ident = self.idents.get(origin.index())?;
        Some(Subject { slot: origin.0, stamp: ident.stamp(), name: ident.name_atom() })
    }

    /// The identifier of an imported module; its slot follows the
    /// variables'.
    fn import_subject(&self, import: ImportId) -> Subject {
        let id = &self.bir.pools.j_modules[import.index()].id;
        Subject { slot: index(self.bir.vars.len() + import.index()), stamp: id.stamp(), name: id.name_atom() }
    }
}

/// Whether nodes of `op` are statements. Constant.
fn is_statement(op: Op) -> bool {
    matches!(
        op,
        Op::SBlock
            | Op::SDecl
            | Op::SExp
            | Op::SIf
            | Op::SWhile
            | Op::SForRangeExisting
            | Op::SForRange
            | Op::SForOf
            | Op::SForAwaitOf
            | Op::SSwitch
            | Op::SReturn
            | Op::SThrow
            | Op::STry
            | Op::SBreak
            | Op::SContinue
            | Op::SDebugger
            | Op::SRest
    )
}

/// The free lists of the live rows that are no copies, as identifiers, for
/// the comparison with the pass (`emit::naming::compare_with_pass`). Check
/// mode only. Cost: one step per row and per entry; allocates the result.
pub(crate) fn free_lists(bir: &Bir, idents: &[crate::ident::Ident]) -> crate::emit::FreeLists {
    let log = &bir.js_scope.as_ref().expect("lowering scope").names;
    let mut lists = crate::emit::FreeLists::default();
    for (row, info) in log.rows.iter().enumerate().skip(1) {
        if info.flags & ScopeRow::CLOSED == 0 || info.flags & ScopeRow::COPY != 0 {
            continue;
        }
        if bir.func_owners.get(info.function.index()).copied().flatten().is_none() {
            continue;
        }
        for &entry in log.free(ScopeId(row as u32)) {
            match (entry.as_var(), entry.as_import()) {
                (Some(var), _) => {
                    if let Some(&ident) = idents.get(bir.vars.j_origin[var.index()].index()) {
                        lists.idents.push(ident);
                    }
                }
                (None, Some(import)) => lists.idents.push(bir.pools.j_modules[import.index()].id),
                (None, None) => unreachable!("a free entry is a variable or an import"),
            }
        }
        lists.ends.push(index(lists.idents.len()));
    }
    lists
}

#[cfg(test)]
mod tests {
    use super::*;

    impl Log {
        /// Room for a repeat of what the log holds, for the tests that
        /// lower the same input twice and count the second run's
        /// allocations (`Scope::reserve_repeat`).
        pub(crate) fn reserve_repeat(&mut self) {
            self.rows.reserve(self.rows.len());
            self.free.reserve(self.free.len());
            self.of_function.reserve(self.of_function.len());
            self.home.reserve(self.home.len());
            self.seen.reserve(self.seen.len());
            self.seen_import.reserve(self.seen_import.len());
        }
    }

    #[test]
    fn row_sizes() {
        assert_eq!(std::mem::size_of::<ScopeId>(), 4);
        assert_eq!(std::mem::size_of::<FreeRef>(), 4);
        assert_eq!(std::mem::size_of::<ScopeRow>(), 16);
        assert_eq!(std::mem::size_of::<Open>(), 16);
        assert_eq!(std::mem::size_of::<Frame>(), 12);
        assert_eq!(std::mem::size_of::<Program<'_>>(), 64);
        assert_eq!(std::mem::size_of::<Replayed>(), 48);
    }

    #[test]
    fn a_free_entry_is_a_variable_or_an_import() {
        let (var, import) = (FreeRef::var(VarId(7)), FreeRef::import(ImportId(7)));
        assert_eq!((var.as_var(), var.as_import()), (Some(VarId(7)), None));
        assert_eq!((import.as_var(), import.as_import()), (None, Some(ImportId(7))));
        // Variables sort before imports; the free list is sorted by
        // identifier, not by this order.
        assert!(var < import);
    }

    #[test]
    fn default_storage_is_empty() {
        let log = Log::default();
        assert!(log.rows.is_empty() && log.free.is_empty() && log.of_function.is_empty());
        assert!(log.home.is_empty() && log.seen.is_empty() && log.seen_import.is_empty());
        assert!(log.open.is_empty() && log.run.is_empty() && log.children.is_empty());
        assert!(log.pending.is_empty());
        assert_eq!((log.steps, log.adopted_nodes), (0, 0));
        let scratch = Scratch::default();
        assert!(scratch.marks.is_empty() && scratch.next.is_empty() && scratch.frames.is_empty() && scratch.reservation.is_empty());
        let program = Program { imports: &[], reservations: &[], exports: &[], raw: &[] };
        assert_eq!(program.imports.len() + program.reservations.len() + program.exports.len() + program.raw.len(), 0);
        assert_eq!(Replayed::default().steps(), 0);
    }

    #[test]
    fn a_new_log_has_the_program_row_and_no_home() {
        let mut log = Log::new(2);
        assert_eq!(log.rows.len(), 1);
        assert_eq!((log.home(VarId(0)), log.home(VarId(1))), (ScopeId::NONE, ScopeId::NONE));
        // A variable created later, bound while no function is open.
        log.variable();
        log.bind(VarId(2));
        assert_eq!(log.home(VarId(2)), ScopeId::PROGRAM);
        // A function of the source arena has no row to copy.
        assert_eq!(log.copied(FuncId(0), FuncId(1)), None);
        assert_eq!(log.steps, 0);
    }

    use crate::bir::lower::scope::Scope;
    use crate::bir::{VarSpan, View};
    use crate::ident::{Ident, IdentFlags};
    use crate::lambda::LamLoc;
    use crate::lambda::lam_compat::LetKind;

    /// A lowering arena under construction and its identifier table. The
    /// arena's hooks feed the log (`Log::variable`, `bind`, `copied`; the
    /// sites); a test calls `open` and `close` as the lowering does.
    struct Unit {
        b: Bir,
        idents: Vec<Ident>,
    }
    impl Unit {
        fn new() -> Self {
            let mut b = Bir::default();
            b.begin_bulk();
            b.js_scope = Some(Scope::new(0));
            // Four imported modules, `M0` to `M3`: a free entry is read
            // through its identifier.
            for name in ["M0", "M1", "M2", "M3"] {
                b.pools.j_modules.push(crate::js_ir::ModuleId {
                    id: Ident::create_persistent(name),
                    kind: crate::js_ir::Kind::Ml,
                    dynamic_import: false,
                });
            }
            Self { b, idents: Vec::new() }
        }
        /// A variable with order and stamp `index + 1`.
        fn local(&mut self, name: &str) -> VarId {
            let stamp = self.idents.len() as u32 + 1;
            self.idents.push(Ident::new(name, stamp as i32, IdentFlags::NONE));
            self.b.new_var_id(Name::new(name), stamp)
        }
        /// `[vars]`: an expression that reads its operands and is no call.
        fn read(&mut self, vars: &[VarId]) -> NodeId {
            let values: Vec<NodeId> = vars.iter().map(|&var| self.b.new_node(View::Var { var }, 0)).collect();
            self.b.new_node(View::JArray { values: &values }, 0)
        }
        fn declare(&mut self, var: VarId, value: NodeId) -> NodeId {
            self.b.new_node(View::SDecl { var, value: Some(value) }, LetKind::Strict as u16)
        }
        fn ret(&mut self, value: NodeId) -> NodeId {
            self.b.new_node(View::SReturn { value }, 0)
        }
        fn effect(&mut self, value: NodeId) -> NodeId {
            self.b.new_node(View::SExp { value }, 0)
        }
        fn block(&mut self, statements: &[NodeId]) -> NodeId {
            self.b.new_node(View::SBlock { statements }, 0)
        }
        /// The header of a function whose parameters are the `len`
        /// variables from `first`.
        fn header(&mut self, first: Option<VarId>, len: u32) -> FuncId {
            let params = VarSpan { start: first.map_or(0, |var| var.0), len };
            self.b.function_header(params, Default::default(), LamLoc::NONE)
        }
        /// The literal over `statements`, closed.
        fn function(&mut self, header: FuncId, statements: &[NodeId]) -> (NodeId, ScopeId) {
            let body = self.block(statements);
            let function = self.b.new_node(View::JFun { body, header }, 0);
            (function, close(&mut self.b, &self.idents, header))
        }
        fn log(&self) -> &Log {
            &self.b.js_scope.as_ref().unwrap().names
        }
        fn free(&self, scope: ScopeId) -> Vec<FreeRef> {
            self.log().free(scope).to_vec()
        }
        fn flags(&self, scope: ScopeId) -> u32 {
            self.log().rows[scope.0 as usize].flags
        }
        /// The names of the unit whose top-level statements are
        /// `statements`, with `raw` as the program's raw JavaScript names,
        /// by variable; and what the replay did.
        fn names(&mut self, statements: &[NodeId], raw: &[&str]) -> (Vec<Option<String>>, Replayed) {
            let root = self.block(statements);
            let raw: Vec<Name> = raw.iter().map(|name| Name::new(name)).collect();
            let program = Program { imports: &[], reservations: &[], exports: &[], raw: &raw };
            let mut printed = Printed::default();
            let replayed = replay(&self.b, root, &self.idents, &program, &mut Tables::default(), &mut Scratch::default(), &mut printed);
            (printed.names.iter().map(|name| name.map(|name| name.to_string())).collect(), replayed)
        }
    }
    fn name(names: &[Option<String>], var: VarId) -> Option<&str> {
        names[var.index()].as_deref()
    }

    /// `let f = p => { let v = [p]; let g = () => { let v' = [captured]; return [v'] }; return [g] }`
    /// (`emit::naming`, `nested`): the unit, its top-level statement, `f`'s
    /// and `g`'s rows, and `v`, `v'`.
    fn nested(capture_outer_local: bool) -> (Unit, NodeId, [ScopeId; 2], [VarId; 2]) {
        let mut u = Unit::new();
        let (f, p, v, g, inner) = (u.local("f"), u.local("p"), u.local("v"), u.local("g"), u.local("v"));
        let outer_header = u.header(Some(p), 1);
        open(&mut u.b);
        let value = u.read(&[p]);
        let declare_v = u.declare(v, value);
        let inner_header = u.header(None, 0);
        open(&mut u.b);
        let captured = u.read(&[if capture_outer_local { v } else { p }]);
        let declare_inner = u.declare(inner, captured);
        let result = u.read(&[inner]);
        let result = u.ret(result);
        let (g_value, g_scope) = u.function(inner_header, &[declare_inner, result]);
        let declare_g = u.declare(g, g_value);
        let result = u.read(&[g]);
        let result = u.ret(result);
        let (f_value, f_scope) = u.function(outer_header, &[declare_v, declare_g, result]);
        let declare_f = u.declare(f, f_value);
        (u, declare_f, [f_scope, g_scope], [v, inner])
    }

    #[test]
    fn a_function_nested_in_a_function_captures_a_local_of_the_outer_one() {
        // Gap 1 (a). The sites of `g` are read at `g`'s close, whatever the
        // enclosing function saw before.
        let (u, _, [f, g], [v, inner]) = nested(true);
        assert_eq!(u.free(g), [FreeRef::var(v)]);
        assert_eq!(u.free(f), []);
        assert_eq!((u.log().home(v), u.log().home(inner)), (f, g));
        let (u, _, [f, g], _) = nested(false);
        // `p` is a parameter of `f`: free in `g`, bound in `f`.
        assert_eq!(u.free(g), [FreeRef::var(VarId(1))]);
        assert_eq!(u.free(f), []);
    }

    #[test]
    fn a_function_that_returns_no_call_is_closed_and_not_eta() {
        let (u, statement, [f, g], _) = nested(true);
        let View::SDecl { value: Some(function), .. } = u.b.view(statement) else { unreachable!() };
        assert!(!eta_shape(&u.b, function));
        for scope in [f, g] {
            assert_eq!(u.flags(scope) & (ScopeRow::CLOSED | ScopeRow::ETA), ScopeRow::CLOSED);
        }
    }

    #[test]
    fn the_free_lists_of_a_unit_are_listed_by_row() {
        // `f` (nothing free), then `g` (`v`).
        let (u, _, _, [v, _]) = nested(true);
        let lists = free_lists(&u.b, &u.idents);
        assert_eq!(lists.idents, [u.idents[v.index()]]);
        assert_eq!(lists.ends, [0, 1]);
    }

    #[test]
    fn a_function_nested_in_a_function_inherits_the_names_of_the_outer_local_it_captures() {
        let (mut u, statement, _, [v, inner]) = nested(true);
        let (names, replayed) = u.names(&[statement], &[]);
        assert_eq!((name(&names, v), name(&names, inner)), (Some("v"), Some("v$1")));
        assert_eq!((replayed.ambiguous_orders, replayed.unnamed_references), (0, 0));
        let (mut u, statement, _, [v, inner]) = nested(false);
        let (names, _) = u.names(&[statement], &[]);
        assert_eq!((name(&names, v), name(&names, inner)), (Some("v"), Some("v")));
    }

    /// `let f = () => { let g = () => [g]; return [g] }; let g' = 1`: the
    /// unit, its two statements, the rows of `f` and `g`, and `g`, `g'`.
    fn recursive() -> (Unit, [NodeId; 2], [ScopeId; 2], [VarId; 2]) {
        let mut u = Unit::new();
        let (f, g, top) = (u.local("f"), u.local("g"), u.local("g"));
        let outer_header = u.header(None, 0);
        open(&mut u.b);
        let inner_header = u.header(None, 0);
        open(&mut u.b);
        let itself = u.read(&[g]);
        let itself = u.ret(itself);
        let (g_value, g_scope) = u.function(inner_header, &[itself]);
        let declare_g = u.declare(g, g_value);
        let result = u.read(&[g]);
        let result = u.ret(result);
        let (f_value, f_scope) = u.function(outer_header, &[declare_g, result]);
        let declare_f = u.declare(f, f_value);
        let one = u.b.new_node(View::JNull, 0);
        let declare_top = u.declare(top, one);
        (u, [declare_f, declare_top], [f_scope, g_scope], [g, top])
    }

    #[test]
    fn a_recursive_inner_function_is_free_in_itself_and_bound_where_it_is_declared() {
        // Gap 1 (b): the home of `g` is written when its declaration is,
        // after `g`'s own scope closed, and belongs to `f` alone.
        let (u, _, [f, g_scope], [g, top]) = recursive();
        assert_eq!(u.free(g_scope), [FreeRef::var(g)]);
        assert_eq!(u.free(f), []);
        assert_eq!((u.log().home(g), u.log().home(top)), (f, ScopeId::PROGRAM));
    }

    #[test]
    fn a_recursive_inner_function_reserves_nothing_in_the_program() {
        let (mut u, statements, _, [g, top]) = recursive();
        let (names, _) = u.names(&statements, &[]);
        assert_eq!((name(&names, g), name(&names, top)), (Some("g"), Some("g")));
    }

    #[test]
    fn a_reference_released_before_the_close_is_not_free() {
        // Section 2: a capture the constructors fold away. `x` is read in
        // the function and the read is released before the close; `y` is
        // read twice and one read is released.
        let mut u = Unit::new();
        let (x, y) = (u.local("x"), u.local("y"));
        let header = u.header(None, 0);
        open(&mut u.b);
        let folded = u.read(&[x, y]);
        u.b.release(folded);
        let kept = u.read(&[y]);
        let kept = u.ret(kept);
        let (_, scope) = u.function(header, &[kept]);
        assert_eq!(u.free(scope), [FreeRef::var(y)]);
    }

    #[test]
    fn the_this_of_a_method_is_recorded_as_read_only_when_the_body_reads_it() {
        // Gap 3.
        for used in [false, true] {
            let mut u = Unit::new();
            let (this, x) = (u.local("o"), u.local("x"));
            let header = u.b.method_header(VarSpan { start: this.0, len: 2 }, Default::default(), LamLoc::NONE);
            open(&mut u.b);
            let result = u.read(&[if used { this } else { x }]);
            let result = u.ret(result);
            let (_, scope) = u.function(header, &[result]);
            assert_eq!(u.flags(scope) & ScopeRow::FIRST_READ != 0, used);
            assert_eq!(u.free(scope), []);
        }
    }

    #[test]
    fn the_this_of_a_method_is_named_only_when_the_body_reads_it() {
        for used in [false, true] {
            let mut u = Unit::new();
            let (m, this, x) = (u.local("m"), u.local("o"), u.local("x"));
            let header = u.b.method_header(VarSpan { start: this.0, len: 2 }, Default::default(), LamLoc::NONE);
            open(&mut u.b);
            let result = u.read(&[if used { this } else { x }]);
            let result = u.ret(result);
            let (value, _) = u.function(header, &[result]);
            let declare = u.declare(m, value);
            let (names, _) = u.names(&[declare], &[]);
            assert_eq!(name(&names, this), used.then_some("o"));
            assert_eq!(name(&names, x), Some("x"));
        }
    }

    #[test]
    fn a_header_replaced_after_the_body_is_the_header_of_the_row() {
        // Gap 2 (`one_unit_arg`, `finish_expression`): the body is built
        // under the header with the unit parameter, the literal with a new
        // header without parameters.
        let mut u = Unit::new();
        let unit = u.local("param");
        let first = u.header(Some(unit), 1);
        open(&mut u.b);
        let null = u.b.new_node(View::JNull, 0);
        let result = u.ret(null);
        let replacement = u.header(None, 0);
        let (_, scope) = u.function(replacement, &[result]);
        assert_eq!(u.log().rows[scope.0 as usize].function, replacement);
        assert_eq!((u.log().scope(replacement), u.log().scope(first)), (Some(scope), None));
        // The dropped parameter is bound nowhere and gets no name.
        assert_eq!(u.log().home(unit), ScopeId::NONE);
    }

    #[test]
    fn the_aliases_of_a_tail_call_loop_are_bound_in_their_function() {
        // Gap 2 (`loop_function_body`): after the body was lowered the
        // header's parameter becomes the copy `_x`, and `let x = _x` is
        // written in front of the body. Both belong to the function: the
        // declaration by its binder, the copy as a parameter at the close.
        let mut u = Unit::new();
        let x = u.local("x");
        open(&mut u.b);
        let result = u.read(&[x]);
        let result = u.ret(result);
        let copy = u.local("_x");
        let header = u.header(Some(copy), 1);
        let alias = u.b.new_node(View::Var { var: copy }, 0);
        let alias = u.declare(x, alias);
        let (_, scope) = u.function(header, &[alias, result]);
        assert_eq!((u.log().home(x), u.log().home(copy)), (scope, scope));
        assert_eq!(u.free(scope), []);
    }

    #[test]
    fn a_statement_is_named_where_it_stands_at_the_end() {
        // Gap 2 and section 2's second hard example: two declarations of
        // one base, built first then second. Names follow the final list,
        // not the order of construction; a statement in no list names
        // nothing.
        let build = || {
            let mut u = Unit::new();
            let (first, second) = (u.local("x"), u.local("x"));
            let (a, b) = (u.b.new_node(View::JNull, 0), u.b.new_node(View::JNull, 0));
            let statements = [u.declare(first, a), u.declare(second, b)];
            (u, statements, [first, second])
        };
        let (mut u, [one, two], [first, second]) = build();
        let (names, replayed) = u.names(&[one, two], &[]);
        assert_eq!((name(&names, first), name(&names, second)), (Some("x"), Some("x$1")));
        assert_eq!(replayed.statements, 2);
        let (mut u, [one, two], [first, second]) = build();
        let (names, _) = u.names(&[two, one], &[]);
        assert_eq!((name(&names, first), name(&names, second)), (Some("x$1"), Some("x")));
        let (mut u, [one, two], [first, second]) = build();
        u.b.release(one);
        let (names, replayed) = u.names(&[two], &[]);
        assert_eq!((name(&names, first), name(&names, second)), (None, Some("x")));
        assert_eq!(replayed.statements, 1);
    }

    #[test]
    fn a_local_takes_the_name_of_an_outer_variable_the_function_does_not_capture() {
        // Section 2, first hard example:
        // `let y = null; let k = a => { let y' = [a]; return [y'] };
        //  let k2 = a => { let y'' = [a, y]; return [y''] }`.
        let mut u = Unit::new();
        let (y, k, a, y1, k2, a2, y2) = (u.local("y"), u.local("k"), u.local("a"), u.local("y"), u.local("k2"), u.local("a"), u.local("y"));
        let null = u.b.new_node(View::JNull, 0);
        let declare_y = u.declare(y, null);
        let mut statements = vec![declare_y];
        for (binder, param, local, captures) in [(k, a, y1, false), (k2, a2, y2, true)] {
            let header = u.header(Some(param), 1);
            open(&mut u.b);
            let value = if captures { u.read(&[param, y]) } else { u.read(&[param]) };
            let declare = u.declare(local, value);
            let result = u.read(&[local]);
            let result = u.ret(result);
            let (value, _) = u.function(header, &[declare, result]);
            statements.push(u.declare(binder, value));
        }
        let (names, _) = u.names(&statements, &[]);
        assert_eq!((name(&names, y), name(&names, y1), name(&names, y2)), (Some("y"), Some("y"), Some("y$1")));
        assert_eq!((name(&names, a), name(&names, a2)), (Some("a"), Some("a")));
    }

    /// `[() => [left], () => [right]]; let a = null; let a' = null`, where
    /// the literals capture the two `a`s declared after them. Returns the
    /// names of `left` and `right` and what the replay did.
    fn two_literals(swapped: bool) -> ([Option<String>; 2], Replayed) {
        let mut u = Unit::new();
        let (first, second) = (u.local("a"), u.local("a"));
        let (left, right) = if swapped { (first, second) } else { (second, first) };
        let mut literals = Vec::new();
        for captured in [left, right] {
            let header = u.header(None, 0);
            open(&mut u.b);
            let body = u.read(&[captured]);
            let body = u.ret(body);
            literals.push(u.function(header, &[body]).0);
        }
        let both = u.b.new_node(View::JArray { values: &literals }, 0);
        let effect = u.effect(both);
        let (a, b) = (u.b.new_node(View::JNull, 0), u.b.new_node(View::JNull, 0));
        let statements = [effect, u.declare(first, a), u.declare(second, b)];
        let (names, replayed) = u.names(&statements, &[]);
        ([names[left.index()].clone(), names[right.index()].clone()], replayed)
    }

    #[test]
    fn two_function_literals_of_one_statement_are_replayed_in_closing_order_and_counted() {
        // The literal that closed first names its variable `a` (the pass:
        // the literal printed first, `emit::naming`,
        // `two_function_literals_of_one_statement_name_what_they_capture_in_print_order`).
        // Both reservations name a variable for the first time in a
        // statement with two literals: both are counted, so a unit where
        // closing order and print order could differ is visible.
        for swapped in [false, true] {
            let (names, replayed) = two_literals(swapped);
            assert_eq!(names, [Some("a".to_string()), Some("a$1".to_string())]);
            assert_eq!(replayed.ambiguous_orders, 2);
        }
    }

    #[test]
    fn two_variables_first_named_by_one_reservation_are_named_in_order() {
        // Section 2, third hard example: `let f = () => [v', v]; let v =
        // null; let v' = null`. The reservation of `f` names both, in
        // `Ident`'s order, whatever the order of the reads.
        let mut u = Unit::new();
        let (v, later, f) = (u.local("v"), u.local("v"), u.local("f"));
        let header = u.header(None, 0);
        open(&mut u.b);
        let body = u.read(&[later, v]);
        let body = u.ret(body);
        let (value, scope) = u.function(header, &[body]);
        assert_eq!(u.free(scope), [FreeRef::var(v), FreeRef::var(later)]);
        let (a, b) = (u.b.new_node(View::JNull, 0), u.b.new_node(View::JNull, 0));
        let statements = [u.declare(f, value), u.declare(v, a), u.declare(later, b)];
        let (names, replayed) = u.names(&statements, &[]);
        assert_eq!((name(&names, v), name(&names, later), name(&names, f)), (Some("v"), Some("v$1"), Some("f")));
        // One literal in the statement: its order is not in question.
        assert_eq!(replayed.ambiguous_orders, 0);
    }

    #[test]
    fn a_suffix_skips_a_raw_javascript_name_of_the_program() {
        // Gap 3.
        let mut u = Unit::new();
        let (first, second) = (u.local("x"), u.local("x"));
        let (a, b) = (u.b.new_node(View::JNull, 0), u.b.new_node(View::JNull, 0));
        let statements = [u.declare(first, a), u.declare(second, b)];
        let (names, _) = u.names(&statements, &["x$1"]);
        assert_eq!((name(&names, first), name(&names, second)), (Some("x"), Some("x$2")));
    }

    #[test]
    fn a_copied_function_gets_a_row_that_shares_the_free_list_of_its_source() {
        // (c): `copy_j` copies a closed literal. The copy's header is new;
        // its row shares the run and is marked, and the source's row stays.
        let mut u = Unit::new();
        let x = u.local("x");
        let header = u.header(None, 0);
        open(&mut u.b);
        let body = u.read(&[x]);
        let body = u.ret(body);
        let (function, scope) = u.function(header, &[body]);
        let rows = u.log().rows.len();
        let copy = crate::bir::j::logic::copy_j(&mut u.b, function);
        let View::JFun { header: copied, .. } = u.b.view(copy) else { unreachable!() };
        assert_ne!(copied, header);
        let copy_scope = u.log().scope(copied).expect("the copy has a row");
        assert_eq!(u.log().rows.len(), rows + 1);
        assert_eq!(u.free(copy_scope), [FreeRef::var(x)]);
        assert_eq!(u.flags(copy_scope) & ScopeRow::COPY, ScopeRow::COPY);
        assert_eq!(u.flags(scope) & ScopeRow::COPY, 0);
        let (source, copied) = (u.log().rows[scope.0 as usize], u.log().rows[copy_scope.0 as usize]);
        assert_eq!((source.free_start, source.free_len), (copied.free_start, copied.free_len));
    }

    #[test]
    fn a_function_copied_into_an_open_scope_keeps_its_parameters_out_of_the_free_list() {
        // The open scope reads the sites of a copy made inside it as its
        // own: the copy's reference to an outer variable is free in the
        // open scope, its reference to its own (fresh) parameter is not.
        let mut u = Unit::new();
        let x = u.local("x");
        let p = u.local("p");
        let inner = u.header(Some(p), 1);
        open(&mut u.b);
        let body = u.read(&[p, x]);
        let body = u.ret(body);
        let (function, inner_scope) = u.function(inner, &[body]);
        assert_eq!(u.free(inner_scope), [FreeRef::var(x)]);
        let outer = u.header(None, 0);
        open(&mut u.b);
        let copy = crate::bir::j::logic::copy_j(&mut u.b, function);
        let View::JFun { header: copied, .. } = u.b.view(copy) else { unreachable!() };
        let parameter = u.b.function_parameter(copied, 0);
        assert_ne!(parameter, p);
        let result = u.ret(copy);
        let (_, outer_scope) = u.function(outer, &[result]);
        assert_eq!(u.log().home(parameter), outer_scope);
        assert_eq!(u.free(outer_scope), [FreeRef::var(x)]);
    }

    #[test]
    fn an_imported_module_is_free_in_every_function_around_its_reference() {
        // The pass counts a module reference as a use (naming.rs
        // `analyze_expr`, `Qualified`). A `JQualified` has a site, as a
        // `Var` has (`Bir::allocate`).
        let mut u = Unit::new();
        let outer = u.header(None, 0);
        open(&mut u.b);
        let inner = u.header(None, 0);
        open(&mut u.b);
        let first = u.b.new_node(View::JQualified { module: ImportId(3), member: None }, 0);
        let second = u.b.new_node(View::JQualified { module: ImportId(3), member: None }, 0);
        let pair = u.b.new_node(View::JArray { values: &[first, second] }, 0);
        let result = u.ret(pair);
        let (value, inner_scope) = u.function(inner, &[result]);
        let result = u.ret(value);
        let (_, outer_scope) = u.function(outer, &[result]);
        assert_eq!(u.free(inner_scope), [FreeRef::import(ImportId(3))]);
        assert_eq!(u.free(outer_scope), [FreeRef::import(ImportId(3))]);
    }

    #[test]
    fn a_module_reference_released_before_the_close_is_not_free() {
        // `(l, r) => Primitive_int.compare(l, r) == 0` prints `l === r`:
        // the constructors release the module reference before the
        // function closes, and the pass, on the finished tree, has no
        // module in the free list. Import 1 is read twice and one read is
        // released; import 0 is read once and released.
        let mut u = Unit::new();
        let header = u.header(None, 0);
        open(&mut u.b);
        let gone = u.b.new_node(View::JQualified { module: ImportId(0), member: None }, 0);
        let half = u.b.new_node(View::JQualified { module: ImportId(1), member: None }, 0);
        let folded = u.b.new_node(View::JArray { values: &[gone, half] }, 0);
        u.b.release(folded);
        let kept = u.b.new_node(View::JQualified { module: ImportId(1), member: None }, 0);
        let kept = u.ret(kept);
        let (_, scope) = u.function(header, &[kept]);
        assert_eq!(u.free(scope), [FreeRef::import(ImportId(1))]);
    }

    #[test]
    fn a_module_reference_that_replaces_a_node_keeps_its_site() {
        // `Bir::replace` moves the reference's content into another slot:
        // the site follows, so the close still reads it and a later
        // release still clears it.
        let mut u = Unit::new();
        let header = u.header(None, 0);
        open(&mut u.b);
        let null = u.b.new_node(View::JNull, 0);
        let result = u.ret(null);
        let module = u.b.new_node(View::JQualified { module: ImportId(2), member: None }, 0);
        u.b.replace(null, module);
        let (_, scope) = u.function(header, &[result]);
        assert_eq!(u.free(scope), [FreeRef::import(ImportId(2))]);
    }

    /// The steps of the log for one function with `references` reads of one
    /// imported module.
    fn steps_of_module_references(references: usize) -> usize {
        let mut u = Unit::new();
        let header = u.header(None, 0);
        open(&mut u.b);
        let values: Vec<NodeId> = (0..references)
            .map(|_| u.b.new_node(View::JQualified { module: ImportId(0), member: None }, 0))
            .collect();
        let body = u.b.new_node(View::JArray { values: &values }, 0);
        let body = u.ret(body);
        let (_, scope) = u.function(header, &[body]);
        assert_eq!(u.free(scope), [FreeRef::import(ImportId(0))]);
        u.log().steps
    }

    #[test]
    fn ten_thousand_module_references_cost_one_step_each() {
        // One step per site at the close, as for a variable; nothing where
        // the reference is built or released.
        let (small, large) = (steps_of_module_references(1_000), steps_of_module_references(10_000));
        assert_eq!(large - small, 9_000);
        assert_eq!(steps_of_module_references(10_000), steps_of_references(10_000));
    }

    /// The steps of the log for one function with `references` reads of one
    /// outer variable.
    fn steps_of_references(references: usize) -> usize {
        let mut u = Unit::new();
        let x = u.local("x");
        let header = u.header(None, 0);
        open(&mut u.b);
        let reads = vec![x; references];
        let body = u.read(&reads);
        let body = u.ret(body);
        let (_, scope) = u.function(header, &[body]);
        assert_eq!(u.free(scope), [FreeRef::var(x)]);
        u.log().steps
    }

    #[test]
    fn ten_thousand_references_cost_one_step_each_at_the_close() {
        // No work where a reference is built; one step per site at the
        // close of the scope it was built in.
        let (small, large) = (steps_of_references(10_000), steps_of_references(20_000));
        assert_eq!(large - small, 10_000);
        assert!(small <= 10_000 + 8, "{small}");
    }

    /// The steps of the log for `depth` functions nested in one another,
    /// each reading `direct` times a local of its own, the innermost also
    /// the outermost variable `x`.
    fn steps_of_nesting(depth: usize, direct: usize) -> usize {
        let mut u = Unit::new();
        let x = u.local("x");
        let mut locals = Vec::new();
        let mut headers = Vec::new();
        for _ in 0..depth {
            headers.push(u.header(None, 0));
            open(&mut u.b);
            locals.push(u.local("v"));
        }
        let mut inner: Option<NodeId> = None;
        for level in (0..depth).rev() {
            let null = u.b.new_node(View::JNull, 0);
            let mut statements = vec![u.declare(locals[level], null)];
            let reads = vec![locals[level]; direct];
            let value = u.read(&reads);
            statements.push(u.effect(value));
            let value = match inner { Some(function) => function, None => u.read(&[x]) };
            statements.push(u.ret(value));
            let (function, scope) = u.function(headers[level], &statements);
            assert_eq!(u.free(scope), [FreeRef::var(x)]);
            inner = Some(function);
        }
        u.log().steps
    }

    #[test]
    fn ten_thousand_nested_functions_read_each_site_at_one_close() {
        // A site inside a closed function is skipped with that function's
        // range: one step per child, not one per site of the child. So the
        // cost per function does not depend on the depth below it, and a
        // function's own sites cost one step each.
        let (small, large) = (steps_of_nesting(5_000, 1), steps_of_nesting(10_000, 1));
        assert!(large <= 2 * small + 8, "{small} -> {large}");
        assert!(large <= 10_000 * 8, "{large}");
        let more_sites = steps_of_nesting(10_000, 3);
        assert_eq!(more_sites - large, 2 * 10_000);
    }

    /// `let f = param => { return param' => [[param], param'] }`, where
    /// `[param]` was built before the inner scope opened (the eta-expansion
    /// of a partial application, `apply_with_arity`): the unit, its
    /// statement, the rows of `f` and the expansion, `param` and `param'`.
    fn partial_application() -> (Unit, NodeId, [ScopeId; 2], [VarId; 2]) {
        let mut u = Unit::new();
        let (f, outer_param) = (u.local("f"), u.local("param"));
        let outer = u.header(Some(outer_param), 1);
        open(&mut u.b);
        let moved = u.read(&[outer_param]);
        open(&mut u.b);
        let fresh = u.local("param");
        let inner = u.header(Some(fresh), 1);
        adopt(&mut u.b, moved);
        let own = u.b.new_node(View::Var { var: fresh }, 0);
        let call = u.b.new_node(View::JArray { values: &[moved, own] }, 0);
        let result = u.ret(call);
        let (expansion, inner_scope) = u.function(inner, &[result]);
        let result = u.ret(expansion);
        let (f_value, outer_scope) = u.function(outer, &[result]);
        let declare_f = u.declare(f, f_value);
        (u, declare_f, [outer_scope, inner_scope], [outer_param, fresh])
    }

    #[test]
    fn an_expression_built_before_the_scope_opened_is_adopted() {
        // G10: the sites of `[param]` are before the scope's range; without
        // `adopt` the expansion's free list is empty.
        let (u, _, [outer, inner], [outer_param, fresh]) = partial_application();
        assert_eq!(u.free(inner), [FreeRef::var(outer_param)]);
        assert_eq!(u.free(outer), []);
        assert_eq!((u.log().home(outer_param), u.log().home(fresh)), (outer, inner));
        // The array and the reference.
        assert_eq!(u.log().adopted_nodes, 2);
    }

    #[test]
    fn the_fresh_parameter_of_a_partial_application_does_not_take_the_name_of_an_adopted_local() {
        // `emit::naming`,
        // `a_function_inherits_the_names_of_what_an_expression_moved_into_it_reads`.
        let (mut u, statement, _, [outer_param, fresh]) = partial_application();
        let (names, replayed) = u.names(&[statement], &[]);
        assert_eq!((name(&names, outer_param), name(&names, fresh)), (Some("param"), Some("param$1")));
        assert_eq!((replayed.ambiguous_orders, replayed.unnamed_references), (0, 0));
    }

    /// `let f = () => { let v = null; return param => [() => { let v' = [v];
    /// return [v'] }, param] }`, where the inner literal was closed before
    /// the expansion's scope opened: the unit, its statement, the rows of
    /// `f`, the literal and the expansion, `v` and `v'`; and the steps and
    /// nodes of the one `adopt`.
    fn adopted_literal() -> (Unit, NodeId, [ScopeId; 3], [VarId; 2], [usize; 2]) {
        let mut u = Unit::new();
        let (f, v, inner_v) = (u.local("f"), u.local("v"), u.local("v"));
        let outer = u.header(None, 0);
        open(&mut u.b);
        let null = u.b.new_node(View::JNull, 0);
        let declare_v = u.declare(v, null);
        let literal_header = u.header(None, 0);
        open(&mut u.b);
        let captured = u.read(&[v]);
        let declare_inner = u.declare(inner_v, captured);
        let result = u.read(&[inner_v]);
        let result = u.ret(result);
        let (literal, literal_scope) = u.function(literal_header, &[declare_inner, result]);
        open(&mut u.b);
        let fresh = u.local("param");
        let inner = u.header(Some(fresh), 1);
        let before = (u.log().steps, u.log().adopted_nodes);
        adopt(&mut u.b, literal);
        let cost = [u.log().steps - before.0, u.log().adopted_nodes - before.1];
        let own = u.b.new_node(View::Var { var: fresh }, 0);
        let call = u.b.new_node(View::JArray { values: &[literal, own] }, 0);
        let result = u.ret(call);
        let (expansion, inner_scope) = u.function(inner, &[result]);
        let result = u.ret(expansion);
        let (f_value, outer_scope) = u.function(outer, &[declare_v, result]);
        let declare_f = u.declare(f, f_value);
        (u, declare_f, [outer_scope, literal_scope, inner_scope], [v, inner_v], cost)
    }

    #[test]
    fn an_adopted_function_literal_gives_its_free_entries_and_is_not_entered() {
        let (u, _, [outer, literal, inner], [v, _], cost) = adopted_literal();
        assert_eq!(u.free(literal), [FreeRef::var(v)]);
        assert_eq!(u.free(inner), [FreeRef::var(v)]);
        assert_eq!(u.free(outer), []);
        // The literal and its one free entry; its body is not read.
        assert_eq!(cost, [2, 1]);
    }

    #[test]
    fn a_function_literal_inside_an_adopted_expression_is_replayed_where_it_stands() {
        // The literal stands in the expansion's `return`: its scope is
        // entered inside the expansion's and inherits the names of `v`.
        let (mut u, statement, _, [v, inner_v], _) = adopted_literal();
        let (names, replayed) = u.names(&[statement], &[]);
        assert_eq!((name(&names, v), name(&names, inner_v)), (Some("v"), Some("v$1")));
        assert_eq!((replayed.ambiguous_orders, replayed.unnamed_references), (0, 0));
    }

    #[test]
    fn the_scrutinee_of_a_dispatch_function_is_adopted() {
        // `external_dispatch`: `(() => { switch (p) {} })()` inside
        // `p => ...`; the scrutinee was lowered before the function.
        let mut u = Unit::new();
        let p = u.local("p");
        let outer = u.header(Some(p), 1);
        open(&mut u.b);
        let arg = u.b.new_node(View::Var { var: p }, 0);
        open(&mut u.b);
        adopt(&mut u.b, arg);
        let header = u.b.switch_header(crate::bir::SwitchInput {
            keys: Vec::new(),
            clauses: Vec::new(),
            constants: 0,
            consts_full: false,
            blocks_full: false,
            has_default: false,
            dispatch: crate::lambda::SwitchDispatch::Direct,
        });
        let switch = u.b.new_node(View::SSwitch { scrutinee: arg, actions: &[], header }, 1);
        let dispatch = u.header(None, 0);
        let (function, inner_scope) = u.function(dispatch, &[switch]);
        let result = u.ret(function);
        let (_, outer_scope) = u.function(outer, &[result]);
        assert_eq!(u.free(inner_scope), [FreeRef::var(p)]);
        assert_eq!(u.free(outer_scope), []);
        assert_eq!(u.log().adopted_nodes, 1);
    }

    #[test]
    fn a_module_reference_in_an_adopted_expression_is_free_in_the_function() {
        let mut u = Unit::new();
        let outer = u.header(None, 0);
        open(&mut u.b);
        let module = u.b.new_node(View::JQualified { module: ImportId(0), member: None }, 0);
        open(&mut u.b);
        adopt(&mut u.b, module);
        let result = u.ret(module);
        let inner = u.header(None, 0);
        let (function, inner_scope) = u.function(inner, &[result]);
        let result = u.ret(function);
        let (_, outer_scope) = u.function(outer, &[result]);
        assert_eq!(u.free(inner_scope), [FreeRef::import(ImportId(0))]);
        assert_eq!(u.free(outer_scope), [FreeRef::import(ImportId(0))]);
    }

    /// The steps and nodes of adopting `[x, x, ...]` with `references`
    /// reads; with `in_literal` the reads are the body of a closed function
    /// literal and the literal is adopted.
    fn cost_of_adopting(references: usize, in_literal: bool) -> [usize; 2] {
        let mut u = Unit::new();
        let x = u.local("x");
        let outer = u.header(None, 0);
        open(&mut u.b);
        let reads = vec![x; references];
        let moved = if in_literal {
            let header = u.header(None, 0);
            open(&mut u.b);
            let body = u.read(&reads);
            let body = u.ret(body);
            u.function(header, &[body]).0
        } else {
            u.read(&reads)
        };
        open(&mut u.b);
        let before = (u.log().steps, u.log().adopted_nodes);
        adopt(&mut u.b, moved);
        let cost = [u.log().steps - before.0, u.log().adopted_nodes - before.1];
        let result = u.ret(moved);
        let inner = u.header(None, 0);
        let (function, scope) = u.function(inner, &[result]);
        assert_eq!(u.free(scope), [FreeRef::var(x)]);
        let result = u.ret(function);
        u.function(outer, &[result]);
        cost
    }

    #[test]
    fn ten_thousand_adopted_nodes_cost_one_step_each_and_a_literal_its_free_entries() {
        let (small, large) = (cost_of_adopting(10_000, false), cost_of_adopting(20_000, false));
        assert_eq!(large[0] - small[0], 10_000);
        // The array and its operands.
        assert_eq!((small[1], large[1]), (10_001, 20_001));
        // A closed literal costs the same whatever its body holds.
        assert_eq!(cost_of_adopting(10, true), cost_of_adopting(10_000, true));
        assert_eq!(cost_of_adopting(10_000, true)[1], 1);
    }

    /// A unit of `count` declarations `let k = () => { let v = [v0]; return
    /// [v] }` after `let v0 = null`: every function captures the outer `v`,
    /// so every local is `v$1`. Returns the unit and its statements.
    fn functions(count: usize) -> (Unit, Vec<NodeId>) {
        let mut u = Unit::new();
        let outer = u.local("v");
        let null = u.b.new_node(View::JNull, 0);
        let mut statements = vec![u.declare(outer, null)];
        for _ in 0..count {
            let (binder, local) = (u.local("k"), u.local("v"));
            let header = u.header(None, 0);
            open(&mut u.b);
            let value = u.read(&[outer]);
            let declare = u.declare(local, value);
            let result = u.read(&[local]);
            let result = u.ret(result);
            let (value, _) = u.function(header, &[declare, result]);
            statements.push(u.declare(binder, value));
        }
        (u, statements)
    }

    #[test]
    fn the_replay_is_linear_in_statements_and_rows() {
        let run = |count: usize| {
            let (mut u, statements) = functions(count);
            let (names, replayed) = u.names(&statements, &[]);
            assert_eq!(name(&names, VarId(2)), Some("v$1"));
            replayed
        };
        let (small, large) = (run(5_000), run(10_000));
        // Per function: its declaration and the two statements of its body;
        // one row; the free variable and the binder reserved; one ancestor
        // (the declaration the literal is the value of).
        assert_eq!(large.statements - small.statements, 3 * 5_000);
        assert_eq!(large.scopes - small.scopes, 5_000);
        assert_eq!(large.reserved - small.reserved, 2 * 5_000);
        assert_eq!((small.ancestors, large.ancestors), (5_000, 10_000));
        assert_eq!(large.steps() - small.steps(), 7 * 5_000);
    }

    #[test]
    fn a_warm_replay_of_a_unit_with_functions_allocates_nothing() {
        // Gap 3: entering a function and assigning a suffixed name in an
        // inherited group allocate nothing once the tables are warm.
        let (mut u, statements) = functions(10_000);
        let root = u.block(&statements);
        let program = Program { imports: &[], reservations: &[], exports: &[], raw: &[] };
        let (mut tables, mut scratch, mut printed) = (Tables::default(), Scratch::default(), Printed::default());
        let first = replay(&u.b, root, &u.idents, &program, &mut tables, &mut scratch, &mut printed);
        let allocations = allocation_counter::measure(|| {
            let second = replay(&u.b, root, &u.idents, &program, &mut tables, &mut scratch, &mut printed);
            assert_eq!(second, first);
        });
        assert_eq!(allocations.count_total, 0, "{allocations:?}");
        assert_eq!(printed.names[2].map(|name| name.to_string()).as_deref(), Some("v$1"));
    }

    #[test]
    fn ten_thousand_literals_on_one_spine_read_each_ancestor_at_most_twice() {
        // `[f1, [f2, [f3, ...]]]` in one statement: literal `k` is `k`
        // arrays below its statement. Each array is read once on the way up
        // and at most once more by the literal that stops at it.
        let run = |count: usize| {
            let mut u = Unit::new();
            let mut literals = Vec::new();
            for _ in 0..count {
                let header = u.header(None, 0);
                open(&mut u.b);
                let null = u.b.new_node(View::JNull, 0);
                let body = u.ret(null);
                literals.push(u.function(header, &[body]).0);
            }
            let mut spine = u.b.new_node(View::JNull, 0);
            for literal in literals.into_iter().rev() {
                spine = u.b.new_node(View::JArray { values: &[literal, spine] }, 0);
            }
            let statement = u.effect(spine);
            u.names(&[statement], &[]).1
        };
        let (small, large) = (run(5_000), run(10_000));
        assert!(large.ancestors <= 3 * 10_000, "{}", large.ancestors);
        assert!(large.ancestors <= 2 * small.ancestors + 8, "{} -> {}", small.ancestors, large.ancestors);
        // Nothing is named for the first time by a reservation.
        assert_eq!(large.ambiguous_orders, 0);
    }
}
