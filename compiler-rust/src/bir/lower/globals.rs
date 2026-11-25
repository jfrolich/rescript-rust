//! The external-shadow decision (THREE_TREES 11.4, "T5 design"): which
//! references to JavaScript globals print as `globalThis.name` because a
//! binding around them prints with the global's name. The legacy pass is
//! `lambda/js_pass_external_shadow.rs`; this takes the same decision once,
//! when the unit's root block exists. `decide` builds the table of names
//! from what the lowering recorded (a binder per variable, the site heads,
//! a count of live references per imported module); the decision is then
//! made in the naming replay's walk (`names::replay`, "T6: the interface"
//! (d)): the walk keeps, per referenced global name, the number of the
//! bindings of that name that cover the place it is at, and a reference
//! found by `JsStmt::globals` is qualified when that number is not zero or
//! an imported module prints with the name.
use super::js::Pools;
use super::js_stmt::JsStmt;
use crate::bir::{Bir, VarId};
use crate::emit::row::Kind;
use crate::ident::Ident;
use crate::name::Name;

/// One referenced global name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Row {
    /// The bindings that print with the name and cover the place the
    /// replay's walk is at.
    binding: u32,
    /// The last referenced global variable with the name, plus one.
    global: u32,
    /// An imported module with a live reference prints with the name.
    imported: bool,
}

/// A link of a row's chain of global variables: the variable, and the link
/// before it plus one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Link {
    item: u32,
    next: u32,
}

/// `Globals::of_var`: the variable is a referenced global (else a binder).
const GLOBAL: u32 = 1 << 31;

/// The tables of the decision, kept on the lowering's scope so that a
/// second unit of the same arena allocates nothing.
#[derive(Default)]
pub(crate) struct Globals {
    /// The row of each referenced global name. Keyed by the interned name:
    /// the legacy pass relates a binding to a global through the spelling
    /// alone, and a `Name` is a process-wide pointer without an index per
    /// unit. The hash is stored in the name. Empty for a unit that
    /// references no JavaScript global.
    names: hashbrown::HashMap<Name, u32, ahash::RandomState>,
    rows: Vec<Row>,
    links: Vec<Link>,
    /// Per variable, when some row is bound: its row plus one, with
    /// `GLOBAL` for a referenced global; zero for a variable of no row.
    /// Sized to the variables only in a unit where a binding or an import
    /// prints with a referenced global's name.
    of_var: Vec<u32>,
    /// A binding or an import prints with a referenced global's name: the
    /// replay's walk counts and decides.
    pub(crate) active: bool,
    /// The rows of the bindings the walk has entered, innermost last.
    covering: Vec<u32>,
    /// Per open list of the walk, where its bindings start in `covering`.
    pub(crate) frames: Vec<u32>,
    /// Variables read, bindings entered and left, statements scanned for
    /// declarations, and the nodes the descent of `JsStmt::globals` read.
    pub(crate) steps: usize,
    /// References that print as `globalThis.name`.
    pub(crate) qualified: usize,
    /// The spellings of the referenced variables that are JavaScript names
    /// (`js_ir::arena::is_raw_js_name`), written by step 1: the raw names
    /// of the naming replay (`names::Program::raw`). May repeat a name.
    pub(crate) raw: Vec<Name>,
}

/// `is_js_global` of the legacy pass.
fn is_js_global(ident: &Ident) -> bool {
    crate::lambda::js_pass_external_shadow::is_js_global(ident)
}

impl Globals {
    /// The row of `name`, added when new. One lookup.
    fn row(&mut self, name: Name) -> u32 {
        let next = self.rows.len() as u32;
        let row = *self.names.entry(name).or_insert(next);
        if row == next {
            self.rows.push(Row { binding: 0, global: 0, imported: false });
        }
        row
    }

    /// Chain `item` before `head`. One push.
    fn link(&mut self, head: u32, item: u32) -> u32 {
        self.links.push(Link { item, next: head });
        self.links.len() as u32
    }

    /// Where the bindings entered from here on start: the mark to give
    /// `leave`. O(1).
    pub(crate) fn mark(&self) -> u32 {
        self.covering.len() as u32
    }

    /// The walk enters the scope of `var`'s binding: when the variable
    /// prints with a referenced global's name, that row's count rises.
    /// O(1): one read of `of_var`, and one step and one push for a binding
    /// of a row.
    pub(crate) fn enter(&mut self, var: VarId) {
        let Some(&entry) = self.of_var.get(var.index()) else { return };
        if entry == 0 || entry & GLOBAL != 0 {
            return;
        }
        let row = entry - 1;
        self.steps += 1;
        self.rows[row as usize].binding += 1;
        self.covering.push(row);
    }

    /// The walk leaves the scopes of the bindings entered since `mark`. One
    /// step per binding left.
    pub(crate) fn leave(&mut self, mark: u32) {
        while self.covering.len() > mark as usize {
            let row = self.covering.pop().expect("a binding entered");
            self.steps += 1;
            self.rows[row as usize].binding -= 1;
        }
    }

    /// The decision for a reference to `var` at the place the walk is at:
    /// a referenced global whose name a binding around it or an imported
    /// module prints with. O(1).
    pub(crate) fn qualifies(&mut self, var: VarId) -> bool {
        let Some(&entry) = self.of_var.get(var.index()) else { return false };
        if entry & GLOBAL == 0 {
            return false;
        }
        let row = self.rows[((entry & !GLOBAL) - 1) as usize];
        let qualified = row.binding != 0 || row.imported;
        self.qualified += usize::from(qualified);
        qualified
    }

    /// The declarations a list binds, entered before its statements are
    /// walked: those of its statements and of the explicit blocks among
    /// them, which the flatten pass splices into the list (the legacy
    /// decision climbed from such a declaration to the list's block). One
    /// step per statement read; a block statement is read where it is
    /// (`JsStmt::with_stmt_at`, `JsStmt::with_block_stmt`), and the read
    /// recurses as deep as explicit blocks nest.
    pub(crate) fn enter_list<B: JsStmt>(&mut self, js: &B, a: &Pools, list: B::L) {
        for at in 0..js.len(a, list) {
            js.with_stmt_at(a, list, at, |statement| self.enter_declarations(js, a, statement));
        }
    }

    /// `enter_list` for one statement. See there.
    fn enter_declarations<B: JsStmt>(&mut self, js: &B, a: &Pools, statement: &B::S) {
        self.steps += 1;
        if let Some(var) = js.declared(a, statement) {
            self.enter(var);
        }
        if js.stmt_kind(a, statement) == Kind::Block && js.stmt_aux(a, statement) == 1 {
            for at in 0..js.block_len(a, statement) {
                js.with_block_stmt(a, statement, at, |inner| self.enter_declarations(js, a, inner));
            }
        }
    }
}

/// Build the table of the decision for the finished unit: the rows of the
/// referenced global names, the bindings and imports that print with one,
/// and, when there is any, the row of each variable (`of_var`) the replay's
/// walk reads. `idents` gives the identifier a variable prints as, by
/// origin. The references are decided by the walk (`names::replay`).
///
/// Cost. A unit that references no JavaScript global: one read per variable
/// (its site head). Otherwise also one read per variable with a binder and
/// one lookup of its printed name, and one read per import; when a binding
/// or a live import prints with a referenced global's name, one write per
/// variable (`of_var`) and one per global variable of a row. Nothing is
/// allocated when the tables have their capacity. The walk's cost is
/// `names::replay`'s: one step per binding of a row entered and left, one
/// per statement scanned for declarations, and the descent of
/// `JsStmt::globals` over every statement it walks; nothing in a unit
/// where no row is bound.
pub(crate) fn decide(bir: &mut Bir, idents: &[Ident]) {
    let Some(mut scope) = bir.js_scope.take() else { return };
    let mut globals = std::mem::take(&mut scope.globals);
    globals.names.clear();
    globals.rows.clear();
    globals.links.clear();
    globals.raw.clear();
    globals.of_var.clear();
    globals.covering.clear();
    globals.frames.clear();
    globals.active = false;
    let ident = |bir: &Bir, var: usize| idents.get(bir.vars.j_origin[var].index()).copied();
    let variables = bir.vars.len();
    globals.steps += variables;
    for (var, head) in scope.site_heads.iter().enumerate().take(variables) {
        if *head == 0 {
            continue;
        }
        let Some(ident) = ident(bir, var) else { continue };
        if crate::js_ir::arena::is_raw_js_name(&ident) && scope.uses[var].remaining > 0 {
            globals.raw.push(ident.name_atom());
        }
        if is_js_global(&ident) {
            let row = globals.row(ident.name_atom());
            let head = globals.rows[row as usize].global;
            globals.rows[row as usize].global = globals.link(head, var as u32);
        }
    }
    if !globals.rows.is_empty() {
        globals.active = bindings(bir, &scope, &mut globals, idents);
        if globals.active {
            for row in 0..globals.rows.len() {
                let mut at = globals.rows[row].global;
                while at != 0 {
                    let Link { item, next } = globals.links[at as usize - 1];
                    at = next;
                    globals.of_var[item as usize] = GLOBAL | (row as u32 + 1);
                }
            }
        }
    }
    scope.globals = globals;
    bir.js_scope = Some(scope);
}

/// Step 2: the row of every binder that prints with a referenced global's
/// name (`of_var`), and the rows an imported module binds. Returns whether
/// any row is bound. One step per variable with a binder and per import.
fn bindings(bir: &Bir, scope: &super::scope::Scope, globals: &mut Globals, idents: &[Ident]) -> bool {
    use crate::js_ir::printer::convert_ident_atom;
    globals.of_var.resize(bir.vars.len(), 0);
    let mut bound = false;
    for var in 0..bir.vars.len() {
        if bir.vars.binder(VarId(var as u32)).is_none() {
            continue;
        }
        globals.steps += 1;
        let Some(ident) = idents.get(bir.vars.j_origin[var].index()) else { continue };
        if ident.is_js() {
            continue;
        }
        if let Some(&row) = globals.names.get(&convert_ident_atom(ident.name_atom())) {
            globals.of_var[var] = row + 1;
            bound = true;
        }
    }
    for (import, module) in bir.pools.j_modules.iter().enumerate() {
        globals.steps += 1;
        if scope.import_uses.get(import).is_none_or(|uses| *uses == 0) || module.dynamic_import || module.id.is_js() {
            continue;
        }
        if let Some(&row) = globals.names.get(&convert_ident_atom(module.id.name_atom())) {
            globals.rows[row as usize].imported = true;
            bound = true;
        }
    }
    bound
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::lower::scope::Scope;
    use crate::bir::{NodeId, View};
    use crate::ident::IdentFlags;
    use crate::lambda::lam_compat::LetKind;

    #[test]
    fn row_sizes() {
        assert_eq!(std::mem::size_of::<Row>(), 12);
        assert_eq!(std::mem::size_of::<Link>(), 8);
    }

    /// An arena with the global `g` (variable 0) and its identifier table.
    fn arena() -> (Bir, Vec<Ident>) {
        let mut b = Bir::default();
        b.begin_bulk();
        b.js_scope = Some(Scope::new(0));
        b.new_var_id(Name::new("g"), 0);
        (b, vec![Ident::create_persistent("g")])
    }
    fn local(b: &mut Bir, idents: &mut Vec<Ident>, name: &str) -> VarId {
        let var = b.new_var_id(Name::new(name), idents.len() as u32);
        idents.push(Ident::new(name, idents.len() as i32, IdentFlags::NONE));
        var
    }
    fn read(b: &mut Bir) -> NodeId {
        b.new_node(View::Var { var: VarId(0) }, 0)
    }
    fn effect(b: &mut Bir, value: NodeId) -> NodeId {
        b.new_node(View::SExp { value }, 0)
    }
    fn block(b: &mut Bir, statements: &[NodeId]) -> NodeId {
        b.new_node(View::SBlock { statements }, 0)
    }
    fn declare(b: &mut Bir, var: VarId) -> NodeId {
        let value = b.new_node(View::JNull, 0);
        b.new_node(View::SDecl { var, value: Some(value) }, LetKind::Strict as u16)
    }
    fn qualified(b: &Bir, node: NodeId) -> bool {
        b.global_qualified(node)
    }
    fn steps(b: &Bir) -> usize {
        b.js_scope.as_ref().unwrap().globals.steps
    }

    #[test]
    fn a_unit_without_a_shadowing_binding_reads_its_variables_and_binders_only() {
        let (mut b, mut idents) = arena();
        let mut statements = Vec::new();
        for _ in 0..10_000 {
            let var = local(&mut b, &mut idents, "x");
            statements.push(declare(&mut b, var));
            let value = read(&mut b);
            statements.push(effect(&mut b, value));
        }
        block(&mut b, &statements);
        decide(&mut b, &idents);
        // 10,001 variables, 10,000 binders; no site is walked.
        assert_eq!(steps(&b), 10_001 + 10_000);
        assert_eq!(b.js_scope.as_ref().unwrap().globals.qualified, 0);
    }

    #[test]
    fn ten_thousand_references_under_one_binding_cost_five_steps_each() {
        // `{ let g = null; g'; g'; ... }`: each reference reads itself, its
        // statement and the marked block, then marks the first two.
        let (mut b, mut idents) = arena();
        let var = local(&mut b, &mut idents, "g");
        let mut statements = vec![declare(&mut b, var)];
        let mut sites = Vec::new();
        for _ in 0..10_000 {
            let value = read(&mut b);
            sites.push(value);
            statements.push(effect(&mut b, value));
        }
        block(&mut b, &statements);
        decide(&mut b, &idents);
        assert!(sites.iter().all(|site| qualified(&b, *site)));
        // Two variables, one binder, one mark; per site: three reads up to
        // the block and two marks.
        assert_eq!(steps(&b), 2 + 1 + 1 + 10_000 * 5);
        assert_eq!(b.js_scope.as_ref().unwrap().globals.qualified, 10_000);
    }

    #[test]
    fn ten_thousand_references_at_depth_ten_thousand_read_each_node_twice() {
        // One chain of 10,000 nested blocks without a binding and 10,000
        // references at the bottom: the first walk reads and marks the
        // chain, every later one stops at its own statement's parent.
        let (mut b, mut idents) = arena();
        let var = local(&mut b, &mut idents, "g");
        let mut statements = Vec::new();
        let mut sites = Vec::new();
        for _ in 0..10_000 {
            let value = read(&mut b);
            sites.push(value);
            statements.push(effect(&mut b, value));
        }
        let mut inner = block(&mut b, &statements);
        for _ in 0..10_000 {
            let condition = b.new_node(View::JNull, 0);
            let statement = b.new_node(View::SIf { condition, then_: inner, else_: None }, 0);
            inner = block(&mut b, &[statement]);
        }
        // The binding is in a sibling function: it shadows nothing here.
        let declaration = declare(&mut b, var);
        let body = block(&mut b, &[declaration]);
        let header = b.function_header(crate::bir::VarSpan { start: 0, len: 0 }, Default::default(), crate::lambda::LamLoc::NONE);
        let function = b.new_node(View::JFun { body, header }, 0);
        let other = effect(&mut b, function);
        let condition = b.new_node(View::JNull, 0);
        let outer = b.new_node(View::SIf { condition, then_: inner, else_: None }, 0);
        block(&mut b, &[outer, other]);
        decide(&mut b, &idents);
        assert!(sites.iter().all(|site| !qualified(&b, *site)));
        // The first site: itself, its statement, 10,001 blocks, 10,001 `if`s
        // and the root, read and marked; the others: three reads, two marks.
        let chain = 2 + 10_001 + 10_001 + 1;
        assert_eq!(steps(&b), 2 + 1 + 1 + 2 * chain + 9_999 * 5);
    }

    #[test]
    fn ten_thousand_bindings_cost_one_mark_each() {
        // 10,000 blocks, each `{ let g = null; g' }`.
        let (mut b, mut idents) = arena();
        let mut statements = Vec::new();
        let mut sites = Vec::new();
        for _ in 0..10_000 {
            let var = local(&mut b, &mut idents, "g");
            let declaration = declare(&mut b, var);
            let value = read(&mut b);
            sites.push(value);
            let statement = effect(&mut b, value);
            let then_ = block(&mut b, &[declaration, statement]);
            let condition = b.new_node(View::JNull, 0);
            statements.push(b.new_node(View::SIf { condition, then_, else_: None }, 0));
        }
        block(&mut b, &statements);
        decide(&mut b, &idents);
        assert!(sites.iter().all(|site| qualified(&b, *site)));
        // 10,001 variables, 10,000 binders, 10,000 marks; per site three
        // reads (itself, its statement, the marked block) and two marks.
        assert_eq!(steps(&b), 10_001 + 10_000 + 10_000 + 10_000 * 5);
    }

    #[test]
    fn a_loop_over_an_existing_variable_binds_nothing_and_the_declaration_of_its_target_covers_it() {
        // `if (null) { let g = null; for (g = ...; ...) { g' } } g'`: the
        // loop's target is a reference to the local `g`, not a binder; the
        // declaration's block covers the loop, so the global inside it is
        // qualified, the one after the `if` is not.
        let (mut b, mut idents) = arena();
        let var = local(&mut b, &mut idents, "g");
        let declaration = declare(&mut b, var);
        let variable = b.new_node(View::Var { var }, 0);
        let finish = b.new_node(View::JNull, 0);
        let inside = read(&mut b);
        let statement = effect(&mut b, inside);
        let body = block(&mut b, &[statement]);
        let looped = b.new_node(View::SForRangeExisting { variable, parts: &[finish, body], label: None }, 0);
        let covered = block(&mut b, &[declaration, looped]);
        let condition = b.new_node(View::JNull, 0);
        let branch = b.new_node(View::SIf { condition, then_: covered, else_: None }, 0);
        let outside = read(&mut b);
        let after = effect(&mut b, outside);
        block(&mut b, &[branch, after]);
        decide(&mut b, &idents);
        assert_eq!(b.vars.binder(var), Some(declaration));
        assert!(qualified(&b, inside));
        assert!(!qualified(&b, outside) && !qualified(&b, variable));
        assert_eq!(b.js_scope.as_ref().unwrap().globals.qualified, 1);
    }

    #[test]
    fn a_second_decision_allocates_nothing() {
        let (mut b, mut idents) = arena();
        let mut statements = Vec::new();
        for _ in 0..10_000 {
            let var = local(&mut b, &mut idents, "g");
            statements.push(declare(&mut b, var));
            let value = read(&mut b);
            statements.push(effect(&mut b, value));
        }
        block(&mut b, &statements);
        decide(&mut b, &idents);
        let allocations = allocation_counter::measure(|| decide(&mut b, &idents));
        assert_eq!(allocations.count_total, 0, "{allocations:?}");
        assert_eq!(b.js_scope.as_ref().unwrap().globals.qualified, 20_000);
    }
}
