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
//! Nothing here is called by the lowering yet (slice T5b-3); the module is
//! compiled for tests only until then.
use crate::bir::{Bir, FuncId, ImportId, NodeId, VarId};
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
    /// `CLOSED`, `ETA`, `THIS_USED`, `COPY`.
    pub(crate) flags: u32,
}
impl ScopeRow {
    /// `close` has written the row.
    pub(crate) const CLOSED: u32 = 1;
    /// The printer eta-reduces the function (`walk::eta_target`): its
    /// binder is named before the reservation and its parameters get no
    /// name.
    pub(crate) const ETA: u32 = 2;
    /// A method whose body reads its first parameter (naming.rs
    /// `analyze_fun`, `method_this`): only then is that parameter named.
    pub(crate) const THIS_USED: u32 = 4;
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
    /// Sites read, run entries read, children skipped, comparisons of the
    /// sort, rows copied.
    pub(crate) steps: usize,
}

impl Log {
    /// A log for a unit of `variables` variables with the program row and
    /// no open function. Cost: two words per variable, allocated once.
    pub(crate) fn new(variables: usize) -> Self {
        let _ = variables;
        todo!("T5b-1")
    }

    /// A variable was created (`Bir::new_var_id`, beside `Scope::push`):
    /// its home is `ScopeId::NONE`. Cost: two pushes; no step.
    pub(crate) fn variable(&mut self) {
        todo!("T5b-1")
    }

    /// The binder of `var` was written (`Bir::bind`, for every binder but a
    /// function's parameters: a declaration, a rest field, a loop variable,
    /// a catch variable): its home is the innermost open scope, the program
    /// when none is open. A variable bound again (a copy made while another
    /// scope is open rebinds nothing: a copy has variables of its own) keeps
    /// the last write. Cost: one write; no step.
    pub(crate) fn bind(&mut self, var: VarId) {
        let _ = var;
        todo!("T5b-1")
    }

    /// A reference to an imported module was built (`Bir::register_kind`,
    /// `JQualified`, `add`): the import joins the innermost open scope's
    /// run unless that scope put it there before. Nothing when no function
    /// is open. A reference released later stays in the run (THREE_TREES
    /// 11.4, "T5 part B as redesigned", (b) Gap 1, the stated limit). Cost:
    /// one read and at most one write and one push; no step.
    pub(crate) fn import_reference(&mut self, import: ImportId) {
        let _ = import;
        todo!("T5b-1")
    }

    /// `Bir::copy_subtree` copied the function literal with header `source`
    /// to one with header `copy` (`bir::j::logic::copy_j`): a row for the
    /// copy that shares the source's free run and flags, with `COPY`. The
    /// copy's own binders print as their origins (`vars.j_origin`), so the
    /// shared list names the same identifiers. Nothing when `source` has no
    /// closed row (a function of the source arena). Cost: one push and one
    /// write; one step.
    pub(crate) fn copied(&mut self, source: FuncId, copy: FuncId) -> Option<ScopeId> {
        let _ = (source, copy);
        todo!("T5b-1")
    }

    /// The row of the function with header `function`. Constant.
    pub(crate) fn scope(&self, function: FuncId) -> Option<ScopeId> {
        let _ = function;
        todo!("T5b-1")
    }

    /// The home of `var`. Constant.
    pub(crate) fn home(&self, var: VarId) -> ScopeId {
        let _ = var;
        todo!("T5b-1")
    }

    /// The free list of a closed scope: sorted by `Ident`'s order (stamp,
    /// then name; an import by its module identifier), without duplicates.
    /// Constant.
    pub(crate) fn free(&self, scope: ScopeId) -> &[FreeRef] {
        let _ = scope;
        todo!("T5b-1")
    }
}

/// A function's scope opens: call it where the lowering starts the body of
/// a function literal (`State::enter`, `View::Fun`), and where it starts
/// building a function of its own (`call.rs`, `ffi_args.rs`, `import.rs`),
/// before the first node of the body is built. Pushes the scope's row and
/// its entry on the open stack. Cost: two pushes; no step.
pub(crate) fn open(bir: &mut Bir) -> ScopeId {
    let _ = bir;
    todo!("T5b-1")
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
/// 3. Each entry of the run whose home is not this row is free. For a
///    method, the first parameter in the run sets `THIS_USED`.
/// 4. The free entries are sorted by `Ident`'s order and written, without
///    duplicates, as the row's run of `Log::free`; `ETA` is `eta_shape` of
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
pub(crate) fn close(bir: &mut Bir, function: FuncId) -> ScopeId {
    let _ = (bir, function);
    todo!("T5b-1")
}

/// Whether the printer eta-reduces the function literal `function`
/// (`emit::walk::eta_target`, on the finished node): not a method, not
/// `async`, no directive, and the body is one `return callee(arguments)`
/// with a variable or module member as callee and exactly the parameters as
/// arguments, in order. Cost: one step per parameter; the body is not read
/// beyond its one statement.
pub(crate) fn eta_shape(bir: &Bir, function: NodeId) -> bool {
    let _ = (bir, function);
    todo!("T5b-1")
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
/// (not the first one of a method without `THIS_USED`) and the body's list;
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
    let _ = (bir, root, idents, program, tables, scratch, printed);
    todo!("T5b-2")
}

/// The free lists of the live rows that are no copies, as identifiers, for
/// the comparison with the pass (`emit::naming::compare_with_pass`). Check
/// mode only. Cost: one step per row and per entry; allocates the result.
pub(crate) fn free_lists(bir: &Bir, idents: &[crate::ident::Ident]) -> crate::emit::FreeLists {
    let _ = (bir, idents);
    todo!("T5b-3")
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert_eq!(log.steps, 0);
        let scratch = Scratch::default();
        assert!(scratch.marks.is_empty() && scratch.next.is_empty() && scratch.frames.is_empty() && scratch.reservation.is_empty());
        let program = Program { imports: &[], reservations: &[], exports: &[], raw: &[] };
        assert_eq!(program.imports.len() + program.reservations.len() + program.exports.len() + program.raw.len(), 0);
        assert_eq!(Replayed::default().steps(), 0);
    }
}
