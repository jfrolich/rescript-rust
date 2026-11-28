//! The external-shadow decision (THREE_TREES 11.4, "T5 design"): which
//! references to JavaScript globals print as `globalThis.name` because a
//! binding around them prints with the global's name. The legacy pass is
//! `lambda/js_pass_external_shadow.rs`; this takes the same decision once,
//! when the unit's root block exists, from what the lowering recorded where
//! it wrote it: a binder node per variable (`VarTable::binder`), a site per
//! reference (`Scope::sites`), the parent of every node, and a count of live
//! references per imported module. No statement body is read.
use crate::bir::{Bir, NodeId, Op, VarId, View};
use crate::ident::Ident;
use crate::name::Name;

/// A binding whose scope covers its node's whole subtree, a walk that found
/// one above, or a node above which there is none.
const CLEAR: u32 = 1;
const SHADOWED: u32 = 2;
/// A `switch` whose cases declare the name: covers the case blocks, not the
/// discriminant.
const CASES: u32 = 3;

/// One referenced global name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Row {
    /// The last binding that prints with the name, plus one; zero for none.
    binding: u32,
    /// The last referenced global variable with the name, plus one.
    global: u32,
    /// An imported module with a live reference prints with the name.
    imported: bool,
}

/// A link of a row's chain: a binder node or a global variable, and the
/// link before it plus one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Link {
    item: u32,
    next: u32,
}

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
    /// Per node: `epoch << 2 | CLEAR, SHADOWED or CASES`. Allocated when the
    /// first binding prints with a referenced global's name.
    marks: Vec<u32>,
    epoch: u32,
    /// Variables read, bindings marked and ancestors read.
    pub(crate) steps: usize,
    /// References that print as `globalThis.name`.
    pub(crate) qualified: usize,
    /// The spellings of the referenced variables that are JavaScript names
    /// (`js_ir::arena::is_raw_js_name`), written by step 1: the raw names
    /// of the naming replay (`names::Program::raw`). May repeat a name.
    pub(crate) raw: Vec<Name>,
    /// The referenced global names that hold an underscore, with their
    /// rows: the only names a variable of the substitution pass
    /// (`<binder>_<suffix>`, `element_bindings`) can print with. Empty in
    /// almost every unit, which then reads no block declaration.
    underscored: Vec<(Name, u32)>,
    /// The spelling of a substitution variable and its printed form, kept
    /// so that spelling one allocates nothing once they have capacity.
    spelled: String,
    printed: String,
}

/// `is_js_global` of the legacy pass.
fn is_js_global(ident: &Ident) -> bool {
    crate::lambda::js_pass_external_shadow::is_js_global(ident)
}

impl Globals {
    /// The row of `name`, added when new. One lookup; a new row also reads
    /// the name's bytes once for an underscore (`underscored`).
    fn row(&mut self, name: Name) -> u32 {
        let next = self.rows.len() as u32;
        let row = *self.names.entry(name).or_insert(next);
        if row == next {
            self.rows.push(Row { binding: 0, global: 0, imported: false });
            if name.as_str().contains('_') {
                self.underscored.push((name, row));
            }
        }
        row
    }

    /// Chain `item` before `head`. One push.
    fn link(&mut self, head: u32, item: u32) -> u32 {
        self.links.push(Link { item, next: head });
        self.links.len() as u32
    }
}

/// Decide every reference to a JavaScript global of the finished unit and
/// set the bit of the ones the legacy pass would qualify
/// (`Bir::qualify_global`). `idents` gives the identifier a variable prints
/// as, by origin.
///
/// Cost. A unit that references no JavaScript global: one read per variable
/// (its site head). Otherwise also one read per variable with a binder and
/// one lookup of its printed name, and one read per import; when a
/// referenced global's name holds an underscore, the steps of
/// `element_bindings` per declaration of a block. Only when a
/// binding or a live import prints with a referenced global's name: one
/// mark per such binding (plus one step per explicit block around a
/// declaration), and per site of that name its ancestors up to the first
/// marked node, each read at most twice per name (the second read marks it
/// with the result), so the sites of one name cost at most two reads per
/// node of the unit together. Nothing is allocated when the tables have
/// their capacity. The tests in this file assert the counts at 10,000
/// references and at 10,000 bindings.
pub(crate) fn decide(bir: &mut Bir, idents: &[Ident]) {
    let Some(mut scope) = bir.js_scope.take() else { return };
    let mut globals = std::mem::take(&mut scope.globals);
    globals.names.clear();
    globals.rows.clear();
    globals.links.clear();
    globals.raw.clear();
    globals.underscored.clear();
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
        let bound = bindings(bir, &scope, &mut globals, idents);
        if bound {
            rows(bir, &scope, &mut globals);
        }
    }
    scope.globals = globals;
    bir.js_scope = Some(scope);
}

/// Step 2: chain every binder that prints with a referenced global's name
/// to its row, and flag the rows an imported module binds. Returns whether
/// any row is bound. One step per variable with a binder and per import;
/// when a referenced global's name holds an underscore, also the steps of
/// `element_bindings` for each declaration.
fn bindings(bir: &Bir, scope: &super::scope::Scope, globals: &mut Globals, idents: &[Ident]) -> bool {
    use crate::js_ir::printer::convert_ident_atom;
    let mut bound = false;
    for var in 0..bir.vars.len() {
        let Some(binder) = bir.vars.binder(VarId(var as u32)) else { continue };
        globals.steps += 1;
        let Some(ident) = idents.get(bir.vars.j_origin[var].index()) else { continue };
        if ident.is_js() {
            continue;
        }
        if let Some(&row) = globals.names.get(&convert_ident_atom(ident.name_atom())) {
            let head = globals.rows[row as usize].binding;
            globals.rows[row as usize].binding = globals.link(head, binder.0);
            bound = true;
        }
        if !globals.underscored.is_empty() {
            bound |= element_bindings(bir, scope, globals, idents, VarId(var as u32), binder, ident);
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

/// The variables the substitution pass declares for the elements of a
/// block declaration, chained to the rows of the referenced globals they
/// print as. The backend in use runs the external-shadow pass after that
/// pass (lam_compile_main.ml:418-425), so they shadow a global of their
/// name. The pass (js_pass_flatten_and_mark_dead.ml, `subst_map`; Rust
/// `Substitute::statement`) binds `<binder>_<suffix>` before a live
/// `Strict`, `StrictOpt` or `Alias` declaration of an immutable block of
/// two or more elements (an alias of deep constants excepted) for each
/// element that is not simple (`simple_element`). Its variables stand in a
/// block statement beside the declaration, so they are in the
/// declaration's scope: the declaration is chained. A live declaration is
/// one the tail-call pass does not find dead: exported or built at least
/// once (`close::decide`).
///
/// Cost: O(1) for a binder that is not a block declaration; otherwise one
/// step per element (twice for an alias, whose elements are read for deep
/// constants first, one step per node of an element) and, per element that
/// is not simple, O(binder name + suffix bytes) to spell its name into the
/// kept buffers and one string comparison per underscored row. Nothing is
/// allocated once the buffers have their capacity.
fn element_bindings(
    bir: &Bir,
    scope: &super::scope::Scope,
    globals: &mut Globals,
    idents: &[Ident],
    var: VarId,
    binder: NodeId,
    ident: &Ident,
) -> bool {
    use crate::lambda::TagInfo;
    use crate::lambda::lam_compat::LetKind;
    let View::SDecl { value: Some(value), .. } = bir.view(binder) else { return false };
    // The low two bits: the `LetKind` (`JsStmt::stmt_aux`).
    let kind = bir.node(binder).aux() & 0b11;
    let alias = kind == LetKind::Alias as u16;
    if !(alias || kind == LetKind::Strict as u16 || kind == LetKind::StrictOpt as u16) {
        return false;
    }
    // `aux` 0: an immutable block (`bridge_j::mutable`).
    let View::JBlockLit { values, info } = bir.view(value) else { return false };
    if bir.node(value).aux() != 0 {
        return false;
    }
    let origin = bir.vars.j_origin[var.index()];
    let exported = scope.facts.get(origin.index()).is_some_and(|facts| facts.state & super::scope::VarFacts::EXPORTED != 0);
    if !exported && scope.uses[var.index()].built == 0 {
        return false;
    }
    let tag = bir.block_tag(info);
    let count = match tag {
        TagInfo::Record(_) | TagInfo::RecordInlined(_) => tag.logical_field_count(),
        _ => values.len(),
    };
    if count < 2 {
        return false;
    }
    if alias && values.iter().all(|&item| deep_constant(bir, item, &mut globals.steps)) {
        return false;
    }
    let mut bound = false;
    for (index, &item) in values.iter().enumerate() {
        globals.steps += 1;
        if simple_element(bir, idents, item) {
            continue;
        }
        let mut spelled = std::mem::take(&mut globals.spelled);
        spelled.clear();
        spelled.push_str(ident.name());
        spelled.push('_');
        let field = match tag {
            TagInfo::Module(fields) => fields.get(index).map(String::as_str),
            TagInfo::Record(record) => record.fields.get(index).map(|(field, _)| field.as_str()),
            _ => None,
        };
        match field {
            Some(field) => spelled.push_str(field),
            None => {
                use std::fmt::Write;
                write!(spelled, "{index}").expect("writing to a string");
            }
        }
        let mut printed = std::mem::take(&mut globals.printed);
        crate::js_ir::printer::convert_ident_into(&spelled, &mut printed);
        for at in 0..globals.underscored.len() {
            let (name, row) = globals.underscored[at];
            if name.as_str() == printed {
                let head = globals.rows[row as usize].binding;
                globals.rows[row as usize].binding = globals.link(head, binder.0);
                bound = true;
            }
        }
        globals.spelled = spelled;
        globals.printed = printed;
    }
    bound
}

/// `is_simple_block_binding_item` of the substitution pass on a lowered
/// element: a variable that no assignment or JavaScript code may change
/// (`var_may_change`: not `ASSIGNED`, not a JavaScript global), a module
/// member, a number, a string, a template without holes, a boolean or
/// `undefined`. O(1).
fn simple_element(bir: &Bir, idents: &[Ident], item: NodeId) -> bool {
    match bir.view(item) {
        View::Var { var } => {
            !bir.vars.flags(var).contains(crate::bir::VarFlags::ASSIGNED)
                && !idents.get(bir.vars.j_origin[var.index()].index()).is_some_and(is_js_global)
        }
        // `aux` 1: a template without holes (`bridge_j`).
        View::JTemplate { .. } => bir.node(item).aux() == 1,
        View::JQualified { .. } | View::JNumber { .. } | View::JStr { .. } | View::JBool | View::JUndefined => true,
        _ => false,
    }
}

/// `is_deep_constant_block_binding_item` of the substitution pass: a
/// constant, or an optional or an immutable block of them. One step per
/// node of the element it reads; a recursion as deep as the element's
/// nesting of blocks and options.
fn deep_constant(bir: &Bir, item: NodeId, steps: &mut usize) -> bool {
    *steps += 1;
    match bir.view(item) {
        View::JTemplate { .. } => bir.node(item).aux() == 1,
        View::JNumber { .. } | View::JStr { .. } | View::JBool | View::JUndefined => true,
        View::JOptional { value } => deep_constant(bir, value, steps),
        View::JBlockLit { values, .. } => bir.node(item).aux() == 0 && values.iter().all(|&value| deep_constant(bir, value, steps)),
        _ => false,
    }
}

/// Steps 3 and 4, one name at a time: mark the scope of each binding, then
/// decide each site. See `decide` for the cost.
fn rows(bir: &mut Bir, scope: &super::scope::Scope, globals: &mut Globals) {
    if globals.marks.len() < bir.nodes.len() {
        globals.marks.resize(bir.nodes.len(), 0);
    }
    for row in 0..globals.rows.len() {
        let Row { binding, global, imported } = globals.rows[row];
        if binding == 0 && !imported {
            continue;
        }
        globals.epoch += 1;
        let epoch = globals.epoch;
        let mut at = binding;
        while at != 0 {
            let Link { item, next } = globals.links[at as usize - 1];
            at = next;
            globals.steps += 1;
            if let Some((node, kind)) = binding_scope(bir, NodeId(item), &mut globals.steps) {
                globals.marks[node.index()] = epoch << 2 | kind;
            }
        }
        let mut at = global;
        while at != 0 {
            let Link { item, next } = globals.links[at as usize - 1];
            at = next;
            let mut site = scope.site_heads[item as usize];
            while site != 0 {
                let super::scope::Site { node, next } = scope.sites[site as usize - 1];
                site = next;
                if node == NodeId(u32::MAX) {
                    continue;
                }
                if imported || shadowed(bir, globals, epoch, node) {
                    bir.qualify_global(node);
                    globals.qualified += 1;
                }
            }
        }
    }
}

/// The node whose subtree a binding covers, as the legacy pass reads the
/// program after the flatten pass, and how it covers it. A declaration: its
/// nearest enclosing block that is not an explicit block statement (the
/// flatten pass splices those into the list they stand in), or the `switch`
/// when that block is a case. A parameter: the function. A loop variable:
/// the loop statement. A catch variable: the handler block. One step per
/// explicit block around a declaration; constant otherwise.
fn binding_scope(bir: &Bir, binder: NodeId, steps: &mut usize) -> Option<(NodeId, u32)> {
    match bir.view(binder) {
        View::SDecl { .. } | View::SRest { .. } => {
            let mut block = bir.parents[binder.index()]?;
            while bir.node(block).op() == Op::SBlock && bir.node(block).aux() != 0 {
                *steps += 1;
                block = bir.parents[block.index()]?;
            }
            match bir.parents[block.index()] {
                Some(parent) if bir.node(parent).op() == Op::SSwitch => Some((parent, CASES)),
                _ => Some((block, SHADOWED)),
            }
        }
        View::JFun { .. } | View::SForRange { .. } | View::SForOf { .. } | View::SForAwaitOf { .. } => Some((binder, SHADOWED)),
        View::STry { parts, exception: Some(_) } => Some((parts[1], SHADOWED)),
        _ => None,
    }
}

/// Whether a marked scope of `epoch` is above `site`. Reads the ancestors
/// up to the first one marked in this epoch, then marks the ones it passed
/// with the result. At a `switch` marked for its cases the walk stops only
/// when it arrived from a case block.
fn shadowed(bir: &Bir, globals: &mut Globals, epoch: u32, site: NodeId) -> bool {
    let (mut node, mut from) = (site, site);
    let (result, stop) = loop {
        globals.steps += 1;
        let mark = globals.marks[node.index()];
        if mark >> 2 == epoch {
            match mark & 3 {
                CLEAR => break (false, Some(node)),
                SHADOWED => break (true, Some(node)),
                _ if from != node && bir.node(from).op() == Op::SBlock => break (true, Some(node)),
                _ => {}
            }
        }
        match bir.parents[node.index()] {
            Some(parent) => (from, node) = (node, parent),
            None => break (false, None),
        }
    };
    let memo = epoch << 2 | if result { SHADOWED } else { CLEAR };
    let mut node = Some(site);
    while node != stop {
        let at = node.expect("a node below the stop").index();
        globals.steps += 1;
        if globals.marks[at] >> 2 != epoch {
            globals.marks[at] = memo;
        }
        node = bir.parents[at];
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::lower::scope::Scope;
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
    fn ten_thousand_block_declarations_cost_one_step_per_element() {
        // `{ let t = [null, null]; ... (10,000 times); t_0' }` with the
        // global `t_0`: the substitution pass would bind both elements of
        // each block (`t_0`, `t_1`), so each declaration shadows `t_0`.
        let mut b = Bir::default();
        b.begin_bulk();
        b.js_scope = Some(Scope::new(0));
        b.new_var_id(Name::new("t_0"), 0);
        let mut idents = vec![Ident::create_persistent("t_0")];
        let mut statements = Vec::new();
        for _ in 0..10_000 {
            let var = local(&mut b, &mut idents, "t");
            b.js_scope.as_mut().unwrap().uses[var.index()].built = 1;
            let elements = [(); 2].map(|()| b.new_node(View::JNull, 0));
            let info = b.js_info(crate::bir::JsPayload::Block(crate::lambda::TagInfo::Tuple));
            let value = b.new_node(View::JBlockLit { values: &elements, info }, 0);
            statements.push(b.new_node(View::SDecl { var, value: Some(value) }, LetKind::Strict as u16));
        }
        let site = read(&mut b);
        statements.push(effect(&mut b, site));
        block(&mut b, &statements);
        decide(&mut b, &idents);
        assert!(qualified(&b, site));
        // 10,001 variables, 10,000 binders, 20,000 elements, 10,000 marks;
        // the site: three reads up to the marked block and two marks.
        assert_eq!(steps(&b), 10_001 + 10_000 + 20_000 + 10_000 + 5);
        let allocations = allocation_counter::measure(|| decide(&mut b, &idents));
        assert_eq!(allocations.count_total, 0, "{allocations:?}");
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
