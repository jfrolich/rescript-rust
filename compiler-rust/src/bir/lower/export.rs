//! T4a (THREE_TREES 11.4, "T4a as built"): the unit's exports. The last
//! value of the top level is read for the export block where the lowering
//! completes it, and the exports are coerced on top-level rows:
//! O:209 extract_toplevel_exports and C:1099
//! coerce_toplevel_exports_with_name_reservations with the tail-move helpers
//! of the legacy shake module (S). OCaml references name the file under
//! `compiler/core` without its prefix: `coercion.ml` and `compile_main.ml`.
use super::*;
use crate::bir::{JsPayload, NodeFlags, Op};
use crate::lambda::TagInfo;
use crate::name::Name;

/// One top-level statement, in output order. Its index is stable for the
/// whole fold.
#[derive(Clone, Copy, Debug)]
pub(super) struct Row {
    stmt: NodeId,
    bits: u32,
}
impl Row {
    /// A declaration (`SDecl`, `SRest`).
    const DECL: u32 = 1;
    /// The declaration has an initialiser.
    const VALUE: u32 = 2;
    /// The initialiser is a function literal.
    const FUNCTION: u32 = 4;
    /// The statement stands inside a top-level block statement.
    const NESTED: u32 = 8;
    /// A top-level block statement; its statements are the rows after it.
    const BLOCK: u32 = 16;
    /// The declaration moved to the export tail.
    const REMOVED: u32 = 32;
    /// A rebound export was inserted before this row.
    const ANCHOR: u32 = 64;
    /// A rebound export inserted before an `ANCHOR` row; it is written there.
    const INSERTED: u32 = 128;
    /// A declaration after the top level: a rebound export, or an export a
    /// finished top level left undeclared. No statement while the fold runs.
    const TAIL: u32 = 256;
    fn has(self, bits: u32) -> bool {
        self.bits & bits == bits
    }
}

/// S:249 TailMoveInitializerKind.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Qualified,
    Function,
    Literal,
    Other,
}

/// The initialiser of a declaration row, classified once where it is read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Init {
    Absent,
    Literal(NodeId),
    Qualified(NodeId),
    /// A reference to a variable (its origin) and the node.
    Var(VarId, NodeId),
    Fun,
    Other(NodeId),
}

/// S:282 the expression a moved alias is replaced by. Every use is a copy.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Replacement {
    /// A reference to a variable.
    Var(VarId),
    /// A copy of an existing expression: a literal, a module member, or a
    /// chain of static field reads over one.
    Node(NodeId),
    /// A module member without the source metadata of the node it is read from.
    Member(NodeId),
}

/// What one pass over the sites of a variable found, relative to a row.
#[derive(Clone, Copy, Default)]
struct Mentions(u8);
impl Mentions {
    /// A reference in an earlier row.
    const PRIOR: u8 = 1;
    /// A reference in a later row.
    const LATER: u8 = 2;
    /// A reference in a later declaration's initialiser, outside functions.
    const LATER_INITIALISER: u8 = 4;
    /// A reference in a later declaration of a function literal.
    const LATER_FUNCTION: u8 = 8;
    /// A reference in a later row that is not a callee or a `new` target.
    const LATER_UNSAFE: u8 = 16;
    /// A reference in the row itself.
    const OWN: u8 = 32;
    fn has(self, bit: u8) -> bool {
        self.0 & bit != 0
    }
}

/// The tables of the fold. They keep their capacity between units of a test
/// that reuses them; a lowering owns one.
#[derive(Default)]
pub(super) struct Tables {
    /// The values of the exports, detached, in export order.
    values: Vec<NodeId>,
    rows: Vec<Row>,
    /// The first declaration row of each variable plus one. Dense by VarId.
    decl: Vec<u32>,
    /// The export index of each variable plus one. Dense by VarId.
    position: Vec<u32>,
    /// Alias chains: the variables on the chain being walked.
    seen: Vec<bool>,
    trail: Vec<VarId>,
    /// The row and the function bit of an ancestor a site walk has passed:
    /// zero unknown, one in no row, else `(row + 1) << 1 | under a function`.
    /// Dense by node; sized when the first site is read.
    row_of: Vec<u32>,
    path: Vec<NodeId>,
    /// The declaration rows that carry each export's name: first row plus
    /// one by export, next row plus one by row.
    name_head: Vec<u32>,
    name_tail: Vec<u32>,
    name_next: Vec<u32>,
    /// A name is a process-wide interned string, not a handle of the unit.
    names: ahash::AHashMap<Name, u32>,
    /// Rebound exports inserted before a row, by ascending row.
    inserted: Vec<(u32, NodeId)>,
    /// The variable each export selects, in export order.
    pub(super) selected: Vec<VarId>,
    /// The fold is running: the declarations after the top level are not
    /// in the block yet (C:1238).
    folding: bool,
    /// The block was flattened: a moved alias did it (S:160 substitute_after).
    flattened: bool,
    /// The last row plus one with the bit, among the statements of the
    /// flattened block.
    last_function: u32,
    last_plain: u32,
    /// The last row plus one with a top-level effect; `u32::MAX` unread.
    last_effect: u32,
    /// The references to the variable of the last collecting `mentions`
    /// pass that stand in a later row: what `substitute_after` replaces.
    later: Vec<NodeId>,
    /// Rows, exports, alias-chain links, sites and ancestors visited.
    pub(super) steps: usize,
    /// Sites read from a variable's chain, released ones included.
    pub(super) site_visits: usize,
    #[cfg(test)]
    arms: Vec<Arm>,
    #[cfg(test)]
    resolved: Vec<Resolved>,
}

/// The exports of a unit as the lowering hands them over.
#[derive(Default)]
pub(crate) struct Coerced {
    /// The exported identifiers after coercion, in export order.
    pub exports: Vec<Ident>,
    /// The original export identifiers whose name a selected local shadows.
    pub reservations: Vec<Ident>,
    /// The arm of the fold and the arm of the resolution each export took.
    #[cfg(test)]
    pub arms: Vec<(Arm, Resolved)>,
    /// `Tables::steps` and `Tables::site_visits` when the unit was complete.
    #[cfg(test)]
    pub steps: usize,
    #[cfg(test)]
    pub site_visits: usize,
}

/// The arm of C:1099 an export took, recorded for the rule tests.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Arm {
    MovedAlias,
    DeclaredExport,
    DeclaredTarget,
    Undefined,
    MovedReused,
    KeptReused,
    Reused,
    Inserted,
    Rebound,
}

/// The arm of O:30 an export took, recorded for the rule tests.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Resolved {
    KeptFunction,
    SelfAlias,
    ReusableDeclared,
    /// The alias chain; true when it left the selected variable.
    Chain(bool),
}

impl State {
    /// O:209 extract_toplevel_exports and the finished case of
    /// compile_main.ml:390-395. Reads the unit's last value: an export
    /// block gives the export identifiers and leaves its values, detached, in
    /// `Tables::values` in export order; the heads of a comma that ends in
    /// an export block become effect statements; any other value is one
    /// effect and the unit has no export block (`None`). Cost: one step per
    /// comma on the right spine of the value, one per comma operand of a
    /// head, one per export. No allocation: the identifiers are moved out of
    /// the block's payload.
    pub(super) fn extract_exports(
        &mut self,
        value: Option<NodeId>,
        finished: Finished,
    ) -> Option<Vec<Ident>> {
        let mut value = value?;
        if matches!(self.arena.view(value), View::JUndefined) {
            self.arena.release(value);
            return None;
        }
        let mut end = value;
        while let View::JSeq { second, .. } = self.arena.view(end) {
            end = second;
        }
        let block = match self.arena.view(end) {
            View::JBlockLit { info, .. } => matches!(
                self.arena.javascript(info),
                JsPayload::Block(TagInfo::ModuleExport(_))
            )
            .then_some(info),
            _ => None,
        };
        let Some(info) = block else {
            self.push_effect(value);
            return None;
        };
        while let View::JSeq { first, second } = self.arena.view(value) {
            self.arena.detach(first);
            self.arena.detach(second);
            self.arena.release(value);
            self.push_effect(first);
            value = second;
        }
        let mut values = std::mem::take(&mut self.coercion.values);
        values.clear();
        let View::JBlockLit { values: fields, .. } = self.arena.view(value) else {
            unreachable!("the right spine ends in the export block")
        };
        values.extend_from_slice(fields);
        for &field in &values {
            self.arena.detach(field);
        }
        self.arena.release(value);
        let JsPayload::Block(TagInfo::ModuleExport(exports)) =
            &mut self.arena.pools.js[info.index()]
        else {
            unreachable!("checked above")
        };
        let exports = std::mem::take(exports);
        debug_assert_eq!(
            exports.len(),
            values.len(),
            "module export idents and payloads must stay aligned"
        );
        if finished == Finished::True {
            for field in &mut values {
                self.arena.release(*field);
                *field = self.pure_expression(View::JUndefined, 0);
            }
        }
        self.coercion.values = values;
        Some(exports)
    }

    /// O:339 push_effect_expression onto the top-level run. One step per
    /// comma operand of `value`; the scratch vector is reused.
    fn push_effect(&mut self, value: NodeId) {
        let mut effects = std::mem::take(&mut self.scratch);
        debug_assert!(effects.is_empty());
        crate::bir::j::norm::jm14_push_effect_expression(&mut self.arena, value, &mut effects);
        for statement in effects.drain(..) {
            self.statements.push(statement);
        }
        self.scratch = effects;
    }

    /// The variables of the export block `exports`, as the importer recorded
    /// them (`bridge::Imported::export_vars`). Cost: one step per export for
    /// each export block of the unit with as many exports; a unit has one.
    fn export_variables(&mut self, exports: &[Ident], into: &mut Vec<VarId>) {
        let recorded = std::mem::take(&mut self.export_vars);
        let mut at = 0;
        while at < recorded.len() {
            let len = recorded[at] as usize;
            let block = &recorded[at + 1..at + 1 + len];
            if len == exports.len()
                && block
                    .iter()
                    .zip(exports)
                    .all(|(&var, export)| self.idents[var as usize] == *export)
            {
                into.extend(block.iter().map(|&var| VarId(var)));
                self.export_vars = recorded;
                return;
            }
            at += 1 + len;
        }
        unreachable!("the importer records the variables of every export block")
    }

    /// The identity the legacy identifiers have: a variable the lowering
    /// copied stands for its origin. One read.
    fn origin(&self, var: VarId) -> VarId {
        self.arena.vars.j_origin[var.index()]
    }

    /// Write the rows of the top-level run `run` and the tables dense by
    /// variable and by export. Cost: one step per statement of the run and
    /// per statement directly inside a top-level block, and one name lookup
    /// per declaration with an initialiser. No statement body is read.
    fn build_rows(&mut self, run: Span, exports: &[VarId]) {
        let mut t = std::mem::take(&mut self.coercion);
        let variables = self.arena.vars.len();
        t.rows.clear();
        t.decl.clear();
        t.decl.resize(variables, 0);
        t.position.clear();
        t.position.resize(variables, 0);
        t.seen.clear();
        t.seen.resize(variables, false);
        t.row_of.clear();
        t.inserted.clear();
        t.selected.clear();
        #[cfg(test)]
        {
            t.arms.clear();
            t.resolved.clear();
        }
        t.folding = true;
        t.flattened = false;
        t.last_function = 0;
        t.last_plain = 0;
        t.last_effect = u32::MAX;
        t.names.clear();
        t.name_head.clear();
        t.name_head.resize(exports.len(), 0);
        t.name_tail.clear();
        t.name_tail.resize(exports.len(), 0);
        t.name_next.clear();
        for (index, &var) in exports.iter().enumerate() {
            t.steps += 1;
            t.position[var.index()] = index as u32 + 1;
            t.names.entry(self.arena.vars.name(var)).or_insert(index as u32);
        }
        let mut work = std::mem::take(&mut t.path);
        work.clear();
        let mut nested = std::mem::take(&mut self.scratch);
        debug_assert!(nested.is_empty());
        for stmt in self.statements.statements(run) {
            // `nested` holds the statements of the blocks still open, last
            // first; a zero marks where a block ends.
            work.push(stmt);
            let mut depth = 0u32;
            while let Some(stmt) = work.pop() {
                if stmt == NodeId(u32::MAX) {
                    depth -= 1;
                    continue;
                }
                t.steps += 1;
                let row = t.rows.len() as u32;
                let mut bits = if depth > 0 { Row::NESTED } else { 0 };
                match self.arena.view(stmt) {
                    View::SBlock { statements } => {
                        bits |= Row::BLOCK;
                        nested.extend_from_slice(statements);
                        work.push(NodeId(u32::MAX));
                        work.extend(nested.drain(..).rev());
                        depth += 1;
                    }
                    View::SDecl { var, value } => {
                        bits |= Row::DECL;
                        if let Some(value) = value {
                            bits |= Row::VALUE;
                            if self.arena.node(value).op() == Op::JFun {
                                bits |= Row::FUNCTION;
                                t.last_function = row + 1;
                            }
                        }
                        let origin = self.arena.vars.j_origin[var.index()];
                        if t.decl[origin.index()] == 0 {
                            t.decl[origin.index()] = row + 1;
                        }
                        if value.is_some() {
                            if let Some(&export) = t.names.get(&self.arena.vars.name(origin)) {
                                t.name_next.resize(row as usize + 1, 0);
                                let tail = &mut t.name_tail[export as usize];
                                if *tail == 0 {
                                    t.name_head[export as usize] = row + 1;
                                } else {
                                    t.name_next[*tail as usize - 1] = row + 1;
                                }
                                *tail = row + 1;
                            }
                        }
                    }
                    View::SRest { var, .. } => {
                        bits |= Row::DECL | Row::VALUE;
                        let origin = self.arena.vars.j_origin[var.index()];
                        if t.decl[origin.index()] == 0 {
                            t.decl[origin.index()] = row + 1;
                        }
                    }
                    _ => {}
                }
                if bits & (Row::DECL | Row::BLOCK) == 0 {
                    t.last_plain = row + 1;
                }
                t.rows.push(Row { stmt, bits });
            }
        }
        t.name_next.resize(t.rows.len(), 0);
        self.scratch = nested;
        t.path = work;
        self.coercion = t;
    }

    /// Whether `row` is a statement of the block the legacy helper reads:
    /// the flattened list (`flat`), or the block as it is. One read.
    fn visible(&self, row: u32, flat: bool) -> bool {
        let bits = self.coercion.rows[row as usize].bits;
        if bits & Row::REMOVED != 0 || (bits & Row::TAIL != 0 && self.coercion.folding) {
            return false;
        }
        if flat || self.coercion.flattened {
            bits & Row::BLOCK == 0
        } else {
            bits & Row::NESTED == 0
        }
    }

    /// S:271 find_declaration: the row that declares `var`. One read.
    fn declaration(&self, var: VarId, flat: bool) -> Option<u32> {
        let row = self.coercion.decl[var.index()].checked_sub(1)?;
        self.visible(row, flat).then_some(row)
    }

    /// The variable, the initialiser and the kind of a declaration row.
    fn declared_by(&self, row: u32) -> (VarId, Option<NodeId>, LetKind) {
        let stmt = self.coercion.rows[row as usize].stmt;
        let kind = match self.arena.node(stmt).aux() & 3 {
            0 => LetKind::Strict,
            1 => LetKind::Alias,
            2 => LetKind::StrictOpt,
            _ => LetKind::Variable,
        };
        match self.arena.view(stmt) {
            View::SDecl { var, value } => (self.origin(var), value, kind),
            View::SRest { var, .. } => (self.origin(var), Some(stmt), kind),
            _ => unreachable!("a declaration row"),
        }
    }

    /// S:36 is_literal. One read.
    fn is_literal(&self, node: NodeId) -> bool {
        matches!(
            self.arena.node(node).op(),
            Op::JNumber | Op::JStr | Op::JBool | Op::JUndefined | Op::JNull
        )
    }

    /// Classify an expression as an initialiser. One read.
    fn classify(&self, node: NodeId) -> Init {
        match self.arena.view(node) {
            View::Var { var } => Init::Var(self.origin(var), node),
            View::JQualified { .. } => Init::Qualified(node),
            View::JFun { .. } => Init::Fun,
            _ if self.is_literal(node) => Init::Literal(node),
            _ => Init::Other(node),
        }
    }

    /// The initialiser of a declaration row. Two reads.
    fn initialiser(&self, row: u32) -> Init {
        match self.declared_by(row) {
            (_, None, _) => Init::Absent,
            (_, Some(value), _) if value == self.coercion.rows[row as usize].stmt => {
                Init::Other(value)
            }
            (_, Some(value), _) => self.classify(value),
        }
    }

    /// Enter `var` on the alias chain being walked; false when it is on it.
    fn enter_chain(&mut self, var: VarId) -> bool {
        self.coercion.steps += 1;
        if std::mem::replace(&mut self.coercion.seen[var.index()], true) {
            return false;
        }
        self.coercion.trail.push(var);
        true
    }

    /// Forget the chain. One step per variable entered.
    fn leave_chain(&mut self) {
        while let Some(var) = self.coercion.trail.pop() {
            self.coercion.seen[var.index()] = false;
        }
    }

    /// S:364 resolve_tail_move_initializer_kind. One step per declaration on
    /// the alias chain of `start`.
    fn chain_kind(&mut self, start: VarId, flat: bool) -> Option<Kind> {
        let mut current = start;
        let kind = loop {
            if !self.enter_chain(current) {
                break None;
            }
            let Some(row) = self.declaration(current, flat) else {
                break None;
            };
            match self.initialiser(row) {
                Init::Fun => break Some(Kind::Function),
                Init::Qualified(_) => break Some(Kind::Qualified),
                Init::Literal(_) => break Some(Kind::Literal),
                Init::Var(next, _) => current = next,
                Init::Absent | Init::Other(_) => break None,
            }
        };
        self.leave_chain();
        kind
    }

    /// S:256 same_name_export_initializer_kind. Cost: that of `chain_kind`.
    fn initialiser_kind(&mut self, init: Init, flat: bool) -> Kind {
        match init {
            Init::Literal(_) => Kind::Literal,
            Init::Qualified(_) => Kind::Qualified,
            Init::Var(target, _) => self.chain_kind(target, flat).unwrap_or(Kind::Other),
            Init::Absent | Init::Fun | Init::Other(_) => Kind::Other,
        }
    }

    /// S:339 tail_move_materialized_root_ident. One step per declaration on
    /// the same-name alias chain.
    fn materialized_root(&mut self, init: Init, flat: bool) -> Option<VarId> {
        let Init::Var(mut current, _) = init else {
            return None;
        };
        let root = loop {
            if !self.enter_chain(current) {
                break None;
            }
            let Some(row) = self.declaration(current, flat) else {
                break None;
            };
            match self.initialiser(row) {
                Init::Absent => break Some(current),
                Init::Var(next, _)
                    if self.arena.vars.name(next) == self.arena.vars.name(current) =>
                {
                    current = next
                }
                _ => break Some(current),
            }
        };
        self.leave_chain();
        root
    }

    /// S:282 resolve_tail_move_replacement_expression. `start` is the
    /// expression the walk starts from: an existing node, or a reference to
    /// a variable the legacy code builds for the walk. One step per
    /// declaration on the same-name alias chain.
    fn replacement(
        &mut self,
        start: Result<NodeId, VarId>,
        rebound: VarId,
        prefer_materialized_root: bool,
        flat: bool,
    ) -> Replacement {
        let unresolved = match start {
            Ok(node) => Replacement::Node(node),
            Err(var) => Replacement::Var(var),
        };
        let mut current = match start {
            Ok(node) => match self.arena.view(node) {
                View::Var { var } => self.origin(var),
                _ => return unresolved,
            },
            Err(var) => var,
        };
        let resolved = loop {
            if !self.enter_chain(current) {
                break unresolved;
            }
            let Some(row) = self.declaration(current, flat) else {
                break Replacement::Var(current);
            };
            let (_, _, kind) = self.declared_by(row);
            let init = self.initialiser(row);
            // lam_pass_lets_dce.ml:21-23 substitutes Strict, Alias and
            // StrictOpt only: stop at a Variable binding.
            if init == Init::Absent || kind == LetKind::Variable {
                break Replacement::Var(current);
            }
            match init {
                Init::Qualified(node) => {
                    break if current == rebound {
                        Replacement::Member(node)
                    } else {
                        Replacement::Var(current)
                    };
                }
                Init::Var(next, _)
                    if self.arena.vars.name(next) == self.arena.vars.name(current) =>
                {
                    current = next
                }
                Init::Literal(node) => {
                    break if prefer_materialized_root && current != rebound {
                        Replacement::Var(current)
                    } else {
                        Replacement::Node(node)
                    };
                }
                _ => break Replacement::Var(current),
            }
        };
        self.leave_chain();
        resolved
    }

    /// The module member a replacement reads, if it is one. One read.
    fn member_of(&self, replacement: Replacement) -> Option<(crate::bir::ImportId, Option<crate::bir::StrId>)> {
        let (Replacement::Node(node) | Replacement::Member(node)) = replacement else {
            return None;
        };
        match self.arena.view(node) {
            View::JQualified { module, member } => Some((module, member)),
            _ => None,
        }
    }

    /// S:428 ml_module_field_tail_move_replacement and S:414 its same-name
    /// form. Two reads.
    fn is_ml_member(&self, replacement: Replacement, name: Option<Name>) -> bool {
        self.member_of(replacement).is_some_and(|(module, member)| {
            self.arena.pools.j_modules[module.index()].kind == crate::js_ir::op::Kind::Ml
                && name.is_none_or(|name| {
                    member.is_some_and(|member| self.arena.text(member) == name.as_str())
                })
        })
    }

    /// The kind of a replacement as an initialiser (S:256 on the replacement).
    fn replacement_kind(&mut self, replacement: Replacement, flat: bool) -> Kind {
        match replacement {
            Replacement::Var(var) => self.chain_kind(var, flat).unwrap_or(Kind::Other),
            Replacement::Member(_) => Kind::Qualified,
            Replacement::Node(node) => {
                let init = self.classify(node);
                self.initialiser_kind(init, flat)
            }
        }
    }

    /// O:112 collect_declared_idents, for one variable: a declaration at the
    /// top level, or below it through `if` and block statements only. Reads
    /// the tables as they were when the fold began: a moved declaration
    /// stays declared. Cost: one step per statement between the declaration
    /// and the top level; no step for a top-level declaration.
    fn declared(&mut self, var: VarId) -> bool {
        if self.coercion.decl[var.index()] != 0 {
            return true;
        }
        let Some(mut node) = self.arena.vars.binder(var) else {
            return false;
        };
        if !matches!(self.arena.node(node).op(), Op::SDecl | Op::SRest) {
            return false;
        }
        while let Some(parent) = self.arena.parents[node.index()] {
            self.coercion.steps += 1;
            if !matches!(self.arena.node(parent).op(), Op::SIf | Op::SBlock) {
                return false;
            }
            node = parent;
        }
        true
    }

    /// E:15 js_expr_no_side_effects and S:1053 js_statement_no_side_effects
    /// as S:641 statement_has_toplevel_effect reads them. A declaration, an
    /// expression statement and a return are one read; a compound statement
    /// is read until its first statement with an effect.
    fn has_toplevel_effect(&mut self, row: u32) -> bool {
        let Row { stmt, bits } = self.coercion.rows[row as usize];
        if bits & Row::DECL != 0 {
            return match self.arena.view(stmt) {
                View::SDecl { value, .. } => value.is_some_and(|value| {
                    !self.arena.node(value).flags().contains(NodeFlags::STRICT)
                }),
                _ => true,
            };
        }
        let mut work = std::mem::take(&mut self.coercion.path);
        work.clear();
        work.push(stmt);
        let mut pure = true;
        while let Some(node) = work.pop() {
            self.coercion.steps += 1;
            let ok = match self.arena.view(node) {
                View::SExp { value } | View::SReturn { value } => {
                    self.arena.node(value).flags().contains(NodeFlags::STRICT)
                }
                View::SBlock { .. }
                | View::SIf { .. }
                | View::SWhile { .. }
                | View::SForRange { .. }
                | View::SForRangeExisting { .. }
                | View::SSwitch { .. }
                | View::STry { .. } => {
                    work.extend(self.arena.view(node).children());
                    true
                }
                View::SThrow { .. }
                | View::SDebugger
                | View::SBreak { .. }
                | View::SContinue { .. }
                | View::SDecl { .. }
                | View::SRest { .. }
                | View::SForOf { .. }
                | View::SForAwaitOf { .. } => false,
                _ => self.arena.node(node).flags().contains(NodeFlags::STRICT),
            };
            if !ok {
                pure = false;
                break;
            }
        }
        work.clear();
        self.coercion.path = work;
        !pure
    }

    /// The last row plus one with a top-level effect, read once per unit
    /// from the last row backwards: one step per row after it. It does not
    /// change during the fold: a moved declaration and a replacement are
    /// strictly pure.
    fn last_effect(&mut self) -> u32 {
        if self.coercion.last_effect == u32::MAX {
            let mut row = self.coercion.rows.len() as u32;
            self.coercion.last_effect = 0;
            while row > 0 {
                row -= 1;
                self.coercion.steps += 1;
                let bits = self.coercion.rows[row as usize].bits;
                if bits & (Row::BLOCK | Row::REMOVED | Row::INSERTED | Row::TAIL) == 0
                    && self.has_toplevel_effect(row)
                {
                    self.coercion.last_effect = row + 1;
                    break;
                }
            }
        }
        self.coercion.last_effect
    }

    /// The row a node is in and whether a function literal lies between, as
    /// `(row + 1) << 1 | function`, or one when the node is in no row (an
    /// export value). Each node above a queried reference is entered once
    /// per unit: the walk stops at the first ancestor another walk reached.
    fn row_of(&mut self, node: NodeId) -> u32 {
        let t = &mut self.coercion;
        if t.row_of.is_empty() {
            t.row_of.resize(self.arena.nodes.len(), 0);
            for (index, row) in t.rows.iter().enumerate() {
                t.steps += 1;
                if row.bits & (Row::REMOVED | Row::INSERTED | Row::TAIL) == 0 {
                    t.row_of[row.stmt.index()] = (index as u32 + 1) << 1;
                }
            }
        }
        let mut path = std::mem::take(&mut t.path);
        path.clear();
        let mut at = node;
        let mut known = loop {
            if at.index() < t.row_of.len() && t.row_of[at.index()] != 0 {
                break t.row_of[at.index()];
            }
            t.steps += 1;
            path.push(at);
            match self.arena.parents[at.index()] {
                Some(parent) => at = parent,
                None => break 1,
            }
        };
        while let Some(at) = path.pop() {
            if known != 1 && self.arena.nodes[at.index()].op() == Op::JFun {
                known |= 1;
            }
            // The reference itself is not remembered: a replacement frees
            // its slot.
            if at != node && at.index() < t.row_of.len() {
                t.row_of[at.index()] = known;
            }
        }
        t.path = path;
        known
    }

    /// One pass over the sites of `var` for every question the fold asks
    /// about its references relative to the row `index` (S:728
    /// statement_mentions_ident_anywhere, S:632
    /// later_toplevel_initializer_mentions_ident, S:626
    /// later_toplevel_function_mentions_ident, S:394
    /// tail_move_uses_are_safe_to_inline, S:469
    /// replacement_resolves_to_recursive_function). With `collect`, the
    /// references in later rows are kept for `substitute_after`, so that a
    /// reference is read from its chain once. Cost: one step per site of
    /// the variable (one per `Var` node ever built for it, released ones
    /// included), plus `row_of`. No allocation once `later` has its capacity.
    fn mentions(&mut self, var: VarId, index: u32, collect: bool) -> Mentions {
        let mut found = Mentions::default();
        if collect {
            self.coercion.later.clear();
        }
        let Some(scope) = &self.arena.js_scope else {
            unreachable!("the lowering arena records sites")
        };
        let mut at = scope.site_heads[var.index()];
        while at != 0 {
            self.coercion.steps += 1;
            self.coercion.site_visits += 1;
            let site = self.arena.js_scope.as_ref().expect("sites").sites[at as usize - 1];
            at = site.next;
            if site.node == NodeId(u32::MAX) {
                continue;
            }
            let Some(parent) = self.arena.parents[site.node.index()] else {
                continue;
            };
            let place = self.row_of(parent);
            if place == 1 {
                continue;
            }
            let (row, function) = ((place >> 1) - 1, place & 1 != 0);
            if collect && row > index {
                self.coercion.later.push(site.node);
            }
            let bits = self.coercion.rows[row as usize].bits;
            if row < index {
                found.0 |= Mentions::PRIOR;
            } else if row == index {
                found.0 |= Mentions::OWN;
            } else {
                found.0 |= Mentions::LATER;
                if bits & Row::FUNCTION != 0 {
                    found.0 |= Mentions::LATER_FUNCTION;
                }
                if bits & Row::VALUE != 0 && !function {
                    found.0 |= Mentions::LATER_INITIALISER;
                }
                let safe = match self.arena.view(parent) {
                    View::JCall { callee, .. }
                    | View::JFlatCall { callee, .. }
                    | View::JNew { callee, .. } => callee == site.node,
                    View::JTagged { tag, .. } => tag == site.node,
                    _ => false,
                };
                if !safe {
                    found.0 |= Mentions::LATER_UNSAFE;
                }
            }
        }
        found
    }

    /// S:469 replacement_resolves_to_recursive_function: the replacement is
    /// a variable declared as a function literal that refers to itself.
    /// Cost: that of `mentions` for that variable.
    fn is_recursive_function(&mut self, replacement: Replacement) -> bool {
        let Replacement::Var(var) = replacement else {
            return false;
        };
        let Some(row) = self.declaration(var, true) else {
            return false;
        };
        self.coercion.rows[row as usize].has(Row::FUNCTION)
            && self.mentions(var, row, false).has(Mentions::OWN)
    }

    /// S:435 later_toplevel_effect_allows_tail_move, from the facts one
    /// `mentions` pass found. Constant after `last_effect`.
    fn later_effect_allows(
        &mut self,
        index: u32,
        target: Mentions,
        kind: Kind,
        qualified_safe: bool,
        recursive: bool,
    ) -> bool {
        if self.last_effect() <= index + 1 {
            return true;
        }
        if kind == Kind::Literal {
            return true;
        }
        if !target.has(Mentions::LATER) {
            return kind == Kind::Function && recursive;
        }
        match kind {
            Kind::Function => !target.has(Mentions::LATER_UNSAFE),
            Kind::Qualified => qualified_safe,
            Kind::Literal | Kind::Other => false,
        }
    }

    /// A fresh copy of a replacement. A literal, a module member and a
    /// variable are one node; a chain of static field reads is one node per
    /// read.
    fn copy_replacement(&mut self, replacement: Replacement) -> NodeId {
        match replacement {
            Replacement::Var(var) => {
                let copy = self.pure_expression(View::Var { var }, 0);
                self.built(copy)
            }
            Replacement::Member(node) => {
                let View::JQualified { module, member } = self.arena.view(node) else {
                    unreachable!("a module member")
                };
                let aux = self.arena.node(node).aux();
                let copy = self.pure_expression(View::JQualified { module, member }, aux);
                self.built(copy)
            }
            Replacement::Node(node) => {
                // The spine of static reads, innermost last.
                let mut spine = std::mem::take(&mut self.coercion.path);
                spine.clear();
                let mut at = node;
                while let View::JDot { object, .. } = self.arena.view(at) {
                    spine.push(at);
                    at = object;
                }
                let mut copy = self.arena.copy_leaf(at);
                self.built(copy);
                while let Some(read) = spine.pop() {
                    let View::JDot { property, position, .. } = self.arena.view(read) else {
                        unreachable!("a static read")
                    };
                    let aux = self.arena.node(read).aux();
                    let outer = crate::bir::j::member(&mut self.arena, copy, property, position, aux);
                    if let Some(cold) = self.arena.cold(read) {
                        self.arena.set_cold(outer, cold);
                    }
                    if self.arena.node(read).flags().contains(NodeFlags::JS_LOC_PRESENT) {
                        let mut flags = self.arena.node(outer).flags();
                        flags.0 |= NodeFlags::JS_LOC_PRESENT;
                        self.arena.nodes[outer.index()].set_flags(flags);
                    }
                    copy = self.built(outer);
                }
                self.coercion.path = spine;
                copy
            }
        }
    }

    /// S:160 substitute_after: remove the declaration row `index` and
    /// replace every reference the collecting `mentions` pass of the moved
    /// variable found in a later row by a copy of the replacement. Cost:
    /// one write and one copy per such reference; no chain is read again.
    /// The block is flattened from here on.
    fn substitute_after(&mut self, index: u32, replacement: Replacement) {
        let mut later = std::mem::take(&mut self.coercion.later);
        for node in later.drain(..) {
            self.coercion.steps += 1;
            let copy = self.copy_replacement(replacement);
            self.arena.replace(node, copy);
        }
        self.coercion.later = later;
        self.coercion.flattened = true;
        let row = &mut self.coercion.rows[index as usize];
        row.bits |= Row::REMOVED;
    }

    /// Release the statement of a removed row once nothing reads it.
    fn release_row(&mut self, index: u32) {
        let stmt = self.coercion.rows[index as usize].stmt;
        if self.arena.parents[stmt.index()].is_some() {
            self.arena.detach(stmt);
        }
        if !self.coercion.row_of.is_empty() {
            self.coercion.row_of[stmt.index()] = 0;
        }
        self.arena.release(stmt);
    }

    /// B:1420 define, for the export `export`: `let var = value`, as a row
    /// of kind `place` (`INSERTED` or `TAIL`) that carries the export's
    /// name. When the variable is declared already, the declaration binds a
    /// copy that prints as the variable. Constant.
    fn define(&mut self, export: u32, place: u32, var: VarId, value: Option<NodeId>, kind: LetKind) -> NodeId {
        let var = if self.arena.vars.binder(var).is_some() {
            let copy = self.arena.new_var_id(self.arena.vars.name(var), self.arena.vars.order(var));
            let origin = self.origin(var);
            self.arena.vars.j_origin[copy.index()] = origin;
            self.idents.push(self.idents[origin.index()]);
            self.sync_tables();
            copy
        } else {
            var
        };
        let stmt = self.arena.new_node(
            View::SDecl { var, value },
            kind as u16 | ((crate::js_ir::op::UsedStats::default() as u16) << 2),
        );
        self.built(stmt);
        // The declaration is a row of the final block: C:801 and O:30 read it.
        let row = self.coercion.rows.len() as u32;
        let mut bits = Row::DECL | place;
        if let Some(value) = value {
            bits |= Row::VALUE;
            if self.arena.node(value).op() == Op::JFun {
                bits |= Row::FUNCTION;
            }
        }
        self.coercion.rows.push(Row { stmt, bits });
        self.coercion.name_next.push(0);
        let origin = self.origin(var);
        if self.coercion.decl[origin.index()] == 0 {
            self.coercion.decl[origin.index()] = row + 1;
        }
        if value.is_some() {
            let tail = &mut self.coercion.name_tail[export as usize];
            if *tail == 0 {
                self.coercion.name_head[export as usize] = row + 1;
            } else {
                self.coercion.name_next[*tail as usize - 1] = row + 1;
            }
            *tail = row + 1;
        }
        stmt
    }

    /// Give a variable the fold created its entries in the dense tables.
    fn sync_tables(&mut self) {
        let variables = self.arena.vars.len();
        self.coercion.decl.resize(variables, 0);
        self.coercion.position.resize(variables, 0);
        self.coercion.seen.resize(variables, false);
    }

    /// A node the fold built may take the slot of a released one: forget
    /// what `row_of` remembered for the slot. One write.
    fn built(&mut self, node: NodeId) -> NodeId {
        if let Some(entry) = self.coercion.row_of.get_mut(node.index()) {
            *entry = 0;
        }
        node
    }

    /// coercion.ml:140-156 `Ident.rename`: a fresh variable with the name of
    /// `var`. Constant; the interned name is copied, not looked up.
    fn renamed(&mut self, var: VarId) -> VarId {
        let order = self.next_order;
        self.next_order = order.checked_add(1).expect("identifier order capacity");
        let name = self.arena.vars.name(var);
        let fresh = self.arena.new_var_id(name, order);
        self.idents
            .push(Ident::new(name, order as i32, crate::ident::IdentFlags::NONE));
        fresh
    }

    /// The identifier a variable prints as. One read.
    fn ident(&self, var: VarId) -> Ident {
        self.idents[self.origin(var).index()]
    }

    /// S:47 move_same_name_export_alias_to_export_tail. Returns the
    /// replacement and the kind of the moved declaration. Cost: the alias
    /// chains of the value, one `mentions` pass for the target, one for the
    /// materialised root, one for the replacement when it is a function,
    /// and `substitute_after` when the alias moves.
    fn move_alias_to_tail(&mut self, export: VarId, value: NodeId) -> Option<(Replacement, LetKind)> {
        let View::Var { var } = self.arena.view(value) else {
            return None;
        };
        let target = self.origin(var);
        if self.arena.vars.name(target) != self.arena.vars.name(export) {
            return None;
        }
        let index = self.declaration(target, true)?;
        let (_, initialiser, property) = self.declared_by(index);
        let initialiser = initialiser?;
        let init = self.initialiser(index);
        let kind = self.initialiser_kind(init, true);
        if property == LetKind::Variable || kind == Kind::Other {
            return None;
        }
        // S:112-121: a binding that resolves to a literal stays in source
        // order, whatever its kind of `let`.
        if kind == Kind::Literal {
            return None;
        }
        let uses = self.mentions(target, index, true);
        let later_initialiser = uses.has(Mentions::LATER_INITIALISER);
        let prefer_materialized_root = match self.materialized_root(init, true) {
            Some(root) if root != target => {
                later_initialiser || self.mentions(root, index, false).has(Mentions::LATER)
            }
            _ => false,
        };
        let replacement = self.replacement(Ok(initialiser), target, prefer_materialized_root, true);
        let qualified = kind == Kind::Qualified;
        let qualified_safe = self.is_ml_member(replacement, Some(self.arena.vars.name(target)))
            || !uses.has(Mentions::LATER_UNSAFE);
        let recursive = self.is_recursive_function(replacement);
        let blocked = uses.has(Mentions::LATER_FUNCTION)
            || (qualified && self.coercion.last_function > index + 1)
            || replacement == Replacement::Var(target)
            || matches!(replacement, Replacement::Node(node)
                if matches!(self.arena.view(node), View::Var { var } if self.origin(var) == target))
            || uses.has(Mentions::PRIOR)
            || (qualified && !qualified_safe)
            || later_initialiser
            || !self.later_effect_allows(index, uses, kind, qualified_safe, recursive);
        if blocked {
            return None;
        }
        self.substitute_after(index, replacement);
        Some((replacement, property))
    }

    /// S:582 direct_reused_same_name_export_alias_binding: the first
    /// declaration carrying the export's name whose initialiser is the
    /// export's value. One step per declaration of that name.
    fn reused_binding(&mut self, export: u32, value: NodeId) -> Option<u32> {
        let mut at = self.coercion.name_head[export as usize];
        while at != 0 {
            self.coercion.steps += 1;
            let row = at - 1;
            at = self.coercion.name_next[row as usize];
            if !self.visible(row, true) {
                continue;
            }
            if let (_, Some(initialiser), _) = self.declared_by(row) {
                if self.same_reusable_value(initialiser, value) {
                    return Some(row);
                }
            }
        }
        None
    }

    /// O:308 same_reusable_export_value. One step per static read of the
    /// shorter chain.
    fn same_reusable_value(&mut self, mut left: NodeId, mut right: NodeId) -> bool {
        loop {
            self.coercion.steps += 1;
            match (self.arena.view(left), self.arena.view(right)) {
                (View::Var { var: l }, View::Var { var: r }) => {
                    return self.ident(l) == self.ident(r);
                }
                (
                    View::JQualified { module: lm, member: lf },
                    View::JQualified { module: rm, member: rf },
                ) => {
                    return self.arena.pools.j_modules[lm.index()]
                        == self.arena.pools.j_modules[rm.index()]
                        && lf.map(|f| self.arena.text(f)) == rf.map(|f| self.arena.text(f));
                }
                (
                    View::JDot { object: lo, property: lp, position: lpos },
                    View::JDot { object: ro, property: rp, position: rpos },
                ) if self.arena.node(left).aux() == 0 && self.arena.node(right).aux() == 0 => {
                    if self.arena.text(lp) != self.arena.text(rp) || lpos != rpos {
                        return false;
                    }
                    left = lo;
                    right = ro;
                }
                _ => return false,
            }
        }
    }

    /// C:172 reusable_export_value_candidate. One step per static read.
    fn reusable_candidate(&self, mut value: NodeId) -> bool {
        loop {
            match self.arena.view(value) {
                View::Var { .. } | View::JQualified { .. } => return true,
                View::JDot { object, .. } if self.arena.node(value).aux() == 0 => value = object,
                _ => return false,
            }
        }
    }

    /// S:183 move_reused_same_name_export_binding_to_export_tail. Cost: the
    /// declarations of the export's name, the alias chains of the value,
    /// one `mentions` pass for the reused variable and `substitute_after`
    /// when the binding moves.
    fn move_reused_to_tail(&mut self, export: u32, value: NodeId) -> Option<(Replacement, LetKind)> {
        let index = self.reused_binding(export, value)?;
        let (reused, _, property) = self.declared_by(index);
        let replacement = self.replacement(Ok(value), reused, false, true);
        let kind = self.replacement_kind(replacement, true);
        let uses = self.mentions(reused, index, true);
        let qualified_safe = self.is_ml_member(replacement, Some(self.arena.vars.name(reused)))
            || !uses.has(Mentions::LATER_UNSAFE);
        let recursive = self.is_recursive_function(replacement);
        let blocked = property == LetKind::Variable
            || (kind == Kind::Literal
                && (property != LetKind::Alias || self.coercion.last_function <= index + 1))
            || kind == Kind::Other
            || uses.has(Mentions::PRIOR)
            || (kind == Kind::Qualified && !qualified_safe)
            || uses.has(Mentions::LATER_INITIALISER)
            || !self.later_effect_allows(index, uses, kind, qualified_safe, recursive);
        if blocked {
            return None;
        }
        self.substitute_after(index, replacement);
        Some((replacement, property))
    }

    /// O:63 count_materialized_same_name_binding_roots. One step per
    /// declaration carrying the export's name.
    fn materialized_roots(&mut self, export: u32) -> usize {
        let mut count = 0;
        let mut at = self.coercion.name_head[export as usize];
        while at != 0 {
            self.coercion.steps += 1;
            let row = at - 1;
            at = self.coercion.name_next[row as usize];
            if !self.visible(row, true) {
                continue;
            }
            let (var, _, _) = self.declared_by(row);
            let alias = matches!(self.initialiser(row), Init::Var(target, _)
                if self.arena.vars.name(target) == self.arena.vars.name(var));
            count += usize::from(!alias);
        }
        count
    }

    /// O:52 keeps_declared_same_name_function_export_alias. Cost: the alias
    /// chain of the export and the declarations of its name.
    fn keeps_function_alias(&mut self, export: u32, var: VarId) -> bool {
        let Some(row) = self.declaration(var, false) else {
            return false;
        };
        self.coercion.rows[row as usize].has(Row::VALUE)
            && self.chain_kind(var, false) == Some(Kind::Function)
            && self.materialized_roots(export) > 1
    }

    /// O:84 resolve_declared_same_name_self_alias_target. Cost: the
    /// same-name alias chain of the export.
    fn self_alias_target(&mut self, var: VarId) -> Option<VarId> {
        match self.replacement(Err(var), var, false, false) {
            Replacement::Var(target) => {
                (target != var && self.declaration(target, false).is_some()).then_some(target)
            }
            _ => None,
        }
    }

    /// O:248 can_reuse_existing_undefined_export_binding: every statement
    /// after the export's declaration is a declaration with a strictly pure
    /// initialiser that is no function. Constant after `last_effect`.
    fn can_reuse_undefined(&mut self, var: VarId) -> bool {
        let Some(row) = self.declaration(var, true) else {
            return false;
        };
        self.coercion.last_plain <= row + 1
            && self.coercion.last_function <= row + 1
            && self.last_effect() <= row + 1
    }

    /// O:266 insert_rebound_export_before_equivalent_later_binding: when
    /// the statements that declare a later export with this literal are
    /// exactly the end of the block, the export is declared before them.
    /// Constant unless the block ends in such a declaration; then one step
    /// per row of that end and one per later export.
    fn insert_before_equivalent(&mut self, export: u32, var: VarId, value: NodeId, exports: &[VarId]) -> bool {
        if !self.is_literal(value) {
            return false;
        }
        let mut start = None;
        let mut row = self.coercion.rows.len() as u32;
        while row > 0 {
            row -= 1;
            self.coercion.steps += 1;
            if self.coercion.rows[row as usize].bits & (Row::INSERTED | Row::TAIL) != 0 {
                continue;
            }
            if !self.visible(row, false) {
                if self.coercion.rows[row as usize].bits & Row::REMOVED != 0 {
                    continue;
                }
                // A statement inside a block: the block is no declaration.
                break;
            }
            if !self.equivalent_later(row, export, value) {
                break;
            }
            start = Some(row);
            if self.coercion.rows[row as usize].bits & Row::ANCHOR != 0 {
                break;
            }
        }
        let Some(start) = start else {
            return false;
        };
        // The first such declaration must be the one the end starts at.
        for &later in &exports[export as usize + 1..] {
            self.coercion.steps += 1;
            if let Some(row) = self.declaration(later, false) {
                if row < start && self.equivalent_later(row, export, value) {
                    return false;
                }
            }
        }
        let stmt = self.define(export, Row::INSERTED, var, Some(value), LetKind::Strict);
        self.coercion.rows[start as usize].bits |= Row::ANCHOR;
        self.coercion.inserted.push((start, stmt));
        true
    }

    /// The predicate of O:266: a declaration of a later export whose
    /// initialiser equals the literal (B:237 ocaml_eq_expression).
    fn equivalent_later(&self, row: u32, export: u32, value: NodeId) -> bool {
        if !self.coercion.rows[row as usize].has(Row::DECL | Row::VALUE) {
            return false;
        }
        let (var, initialiser, _) = self.declared_by(row);
        let Some(initialiser) = initialiser else {
            return false;
        };
        self.coercion.position[var.index()] > export + 1
            && initialiser != self.coercion.rows[row as usize].stmt
            && crate::bir::j::equal::equal(&self.arena, initialiser, value, &mut 0)
    }

    /// C:1099 coerce_toplevel_exports_with_name_reservations on the rows of
    /// the top-level run `run`: one export at a time, the arms in the legacy
    /// order. Cost: one step per row, per export, per declaration carrying
    /// an export's name, per site of a variable an arm asks about and per
    /// ancestor `row_of` enters; every variable is asked about by at most
    /// one export, because the arms read variables carrying the export's
    /// name. Linear in rows plus references plus the nodes between a
    /// visited reference and its statement: at most 3 steps per row, 8 per
    /// export without an alias chain, and 3 per reference of a moved alias
    /// directly under its statement's expression (the tests at 10,000
    /// assert these), plus one per further link of an alias chain and per
    /// further ancestor.
    pub(super) fn coerce_exports(&mut self, run: Span, idents: Vec<Ident>, finished: Finished) -> Coerced {
        let mut exports = Vec::with_capacity(idents.len());
        self.export_variables(&idents, &mut exports);
        self.build_rows(run, &exports);
        let block_ended = finished == Finished::True;
        let mut selected = std::mem::take(&mut self.coercion.selected);
        let mut reservations = Vec::new();
        self.names.reservations.clear();
        for index in 0..exports.len() as u32 {
            self.coercion.steps += 1;
            let export = exports[index as usize];
            let ident = idents[index as usize];
            let value = self.coercion.values[index as usize];
            // Read before the arms add rows: the rows are the block's.
            let value_var = match self.arena.view(value) {
                View::Var { var } => Some(self.origin(var)),
                _ => None,
            };
            let exact_self_export = value_var == Some(export);
            // coercion.ml:99-111: an export of its own identifier
            // changes the export list only.
            if !exact_self_export {
                if let Some((replacement, property)) = self.move_alias_to_tail(export, value) {
                    let late = self.copy_replacement(replacement);
                    let target = value_var.expect("a moved alias is a variable");
                    let row = self.declaration_row_removed(target);
                    self.release_row(row);
                    self.arena.release(value);
                    self.define(index, Row::TAIL, export, Some(late), property);
                    selected.push(export);
                    #[cfg(test)]
                    self.coercion.arms.push(Arm::MovedAlias);
                    continue;
                }
            }
            if let Some(target) = value_var {
                if self.arena.vars.name(target) == self.arena.vars.name(export) {
                    if self.declared(export) {
                        let chosen = if self.keeps_function_alias(index, export) {
                            export
                        } else {
                            self.self_alias_target(export).unwrap_or(export)
                        };
                        if chosen != export {
                            reservations.push(ident);
                            self.reserve_name(export, ident);
                        }
                        selected.push(chosen);
                        self.arena.release(value);
                        #[cfg(test)]
                        self.coercion.arms.push(Arm::DeclaredExport);
                        continue;
                    }
                    if self.declared(target) {
                        let flat = false;
                        let chosen = match self.replacement(Err(target), target, false, flat) {
                            Replacement::Var(resolved) => resolved,
                            _ => target,
                        };
                        if chosen != export {
                            reservations.push(ident);
                            self.reserve_name(export, ident);
                        }
                        selected.push(chosen);
                        self.arena.release(value);
                        #[cfg(test)]
                        self.coercion.arms.push(Arm::DeclaredTarget);
                        continue;
                    }
                }
            }
            if matches!(self.arena.view(value), View::JUndefined)
                && ((self.declared(export) && self.can_reuse_undefined(export)) || block_ended)
            {
                selected.push(export);
                self.arena.release(value);
                #[cfg(test)]
                self.coercion.arms.push(Arm::Undefined);
                continue;
            }
            if self.reusable_candidate(value) {
                if let Some((replacement, property)) = self.move_reused_to_tail(index, value) {
                    let late = self.copy_replacement(replacement);
                    let row = self.reused_row_removed(index);
                    self.release_row(row);
                    self.arena.release(value);
                    self.define(index, Row::TAIL, export, Some(late), property);
                    selected.push(export);
                    #[cfg(test)]
                    self.coercion.arms.push(Arm::MovedReused);
                    continue;
                }
                if let Some(row) = self.reused_binding(index, value) {
                    let (reused, _, property) = self.declared_by(row);
                    // S:599 keeps_declared_same_name_reusable_export_binding.
                    if reused == export && property != LetKind::Variable {
                        selected.push(export);
                        self.arena.release(value);
                        #[cfg(test)]
                        self.coercion.arms.push(Arm::KeptReused);
                        continue;
                    }
                }
                // O:295 reusable_same_name_export_binding.
                if let Some(reused) = self.reusable_binding(index, export, value) {
                    selected.push(reused);
                    self.arena.release(value);
                    #[cfg(test)]
                    self.coercion.arms.push(Arm::Reused);
                    continue;
                }
            }
            if self.insert_before_equivalent(index, export, value, &exports) {
                selected.push(export);
                #[cfg(test)]
                self.coercion.arms.push(Arm::Inserted);
                continue;
            }
            // coercion.ml:140-156: `Ident.rename` of the export.
            let rebound = self.renamed(export);
            self.sync_tables();
            reservations.push(ident);
            self.reserve_name(export, ident);
            let property = if value_var.is_some() {
                LetKind::Alias
            } else {
                LetKind::Strict
            };
            selected.push(rebound);
            self.define(index, Row::TAIL, rebound, Some(value), property);
            #[cfg(test)]
            self.coercion.arms.push(Arm::Rebound);
        }
        self.coercion.selected = selected;
        let exports = self.resolve_exports(finished);
        Coerced {
            exports,
            reservations,
            #[cfg(test)]
            arms: self
                .coercion
                .arms
                .iter()
                .copied()
                .zip(self.coercion.resolved.iter().copied())
                .collect(),
            #[cfg(test)]
            steps: 0,
            #[cfg(test)]
            site_visits: 0,
        }
    }

    /// Record the reservation `ident` of the export variable `export` for
    /// the naming log's replay, as the subject the naming tables take
    /// (`State::replay_names`). Cost: one push on `reservations`; it
    /// allocates when the pool grows.
    fn reserve_name(&mut self, export: VarId, ident: Ident) {
        self.names.reservations.push(crate::emit::Subject {
            slot: self.arena.vars.j_origin[export.index()].0,
            stamp: ident.stamp(),
            name: ident.name_atom(),
        });
    }

    /// compile_main.ml `declare_undeclared_exports` (C:801) and O:30
    /// resolve_export_aliases, on the rows of the final block: the
    /// declarations after the top level are statements now. A finished top
    /// level gets `let export;` for every export no top-level statement
    /// declares. Each export then resolves in the order of O:42-47: a kept
    /// function alias, the self-alias target, a reusable same-name binding,
    /// the alias chain. Cost: one step per export, per declaration carrying
    /// its name and per declaration on its alias chains.
    fn resolve_exports(&mut self, finished: Finished) -> Vec<Ident> {
        self.coercion.folding = false;
        let mut selected = std::mem::take(&mut self.coercion.selected);
        if finished == Finished::True {
            // The set of declared identifiers is read before any is added:
            // an export selected twice is declared twice (C:806-818).
            let mut undeclared = std::mem::take(&mut self.coercion.trail);
            debug_assert!(undeclared.is_empty());
            for (index, &var) in selected.iter().enumerate() {
                self.coercion.steps += 1;
                if self.declaration(var, false).is_none() {
                    undeclared.push(VarId(index as u32));
                }
            }
            for index in undeclared.drain(..) {
                let var = selected[index.0 as usize];
                self.define(index.0, Row::TAIL, var, None, LetKind::Strict);
            }
            self.coercion.trail = undeclared;
        }
        let mut exports = Vec::with_capacity(selected.len());
        for (index, selection) in selected.iter_mut().enumerate() {
            let (index, var) = (index as u32, *selection);
            self.coercion.steps += 1;
            #[cfg(test)]
            let arm;
            let resolved = if self.keeps_function_alias(index, var) {
                #[cfg(test)]
                {
                    arm = Resolved::KeptFunction;
                }
                var
            } else if let Some(target) = self.self_alias_target(var) {
                #[cfg(test)]
                {
                    arm = Resolved::SelfAlias;
                }
                target
            } else if let Some(reused) = self.reusable_declared(index, var) {
                #[cfg(test)]
                {
                    arm = Resolved::ReusableDeclared;
                }
                reused
            } else {
                let end = self.alias_chain(var);
                #[cfg(test)]
                {
                    arm = Resolved::Chain(end != var);
                }
                end
            };
            #[cfg(test)]
            self.coercion.resolved.push(arm);
            exports.push(self.ident(resolved));
            // The selection is read no more: it becomes the variable of
            // each entry of `Coerced::exports`, which the naming log's
            // replay names last (`State::replay_names`).
            *selection = resolved;
            // The top-level statuses read the export set through the origin.
            let origin = self.origin(resolved);
            let scope = self.arena.js_scope.as_mut().expect("lowering scope");
            scope.facts[origin.index()].state |= super::scope::VarFacts::EXPORTED;
        }
        self.coercion.selected = selected;
        exports
    }

    /// O:101 reusable_declared_same_name_export_alias: another declaration
    /// of the export's name with the export's own initialiser. One step per
    /// declaration of that name.
    fn reusable_declared(&mut self, export: u32, var: VarId) -> Option<VarId> {
        let row = self.declaration(var, true)?;
        let (_, initialiser, _) = self.declared_by(row);
        let initialiser = initialiser?;
        if initialiser == self.coercion.rows[row as usize].stmt {
            return None;
        }
        self.reusable_binding(export, var, initialiser)
    }

    /// O:150 collect_export_aliases, for one variable: the variable its
    /// declaration aliases, when the declaration is in the final block.
    /// Cost: that of `declared_now`.
    fn alias_of(&mut self, var: VarId) -> Option<VarId> {
        if !self.declared_now(var) {
            return None;
        }
        let stmt = match self.declaration(var, true) {
            Some(row) => self.coercion.rows[row as usize].stmt,
            None => self.arena.vars.binder(var)?,
        };
        match self.arena.view(stmt) {
            View::SDecl { value: Some(value), .. } => match self.arena.view(value) {
                View::Var { var } => Some(self.origin(var)),
                _ => None,
            },
            _ => None,
        }
    }

    /// O:112 collect_declared_idents on the final block, for one variable.
    /// Cost: one step per statement between the declaration and the top
    /// level; none for a top-level declaration.
    fn declared_now(&mut self, var: VarId) -> bool {
        if self.declaration(var, true).is_some() {
            return true;
        }
        if self.coercion.decl[var.index()] != 0 {
            // Its top-level declaration moved to the export tail.
            return false;
        }
        self.declared(var)
    }

    /// O:172 resolve_export_alias: follow same-name aliases through declared
    /// variables. One step per declaration on the chain.
    fn alias_chain(&mut self, export: VarId) -> VarId {
        let mut current = export;
        while let Some(target) = self.alias_of(current) {
            if self.arena.vars.name(target) != self.arena.vars.name(export)
                || !self.declared_now(target)
                || !self.enter_chain(current)
            {
                break;
            }
            current = target;
        }
        self.leave_chain();
        current
    }

    /// The row `substitute_after` just removed for `target`.
    fn declaration_row_removed(&self, target: VarId) -> u32 {
        let row = self.coercion.decl[target.index()] - 1;
        debug_assert!(self.coercion.rows[row as usize].has(Row::REMOVED));
        row
    }

    /// The row `substitute_after` just removed among the declarations that
    /// carry the export's name: the only removed one, since names of
    /// exports are distinct. One step per declaration of that name.
    fn reused_row_removed(&mut self, export: u32) -> u32 {
        let mut at = self.coercion.name_head[export as usize];
        loop {
            self.coercion.steps += 1;
            let row = at - 1;
            if self.coercion.rows[row as usize].has(Row::REMOVED) {
                return row;
            }
            at = self.coercion.name_next[row as usize];
        }
    }

    /// O:295 reusable_same_name_export_binding: the first declaration that
    /// carries the export's name, is not the export and is no `Variable`,
    /// with the export's value as initialiser. One step per declaration of
    /// that name.
    fn reusable_binding(&mut self, export: u32, var: VarId, value: NodeId) -> Option<VarId> {
        let mut at = self.coercion.name_head[export as usize];
        while at != 0 {
            self.coercion.steps += 1;
            let row = at - 1;
            at = self.coercion.name_next[row as usize];
            if !self.visible(row, true) {
                continue;
            }
            let (reused, initialiser, property) = self.declared_by(row);
            if reused != var
                && property != LetKind::Variable
                && initialiser.is_some_and(|initialiser| self.same_reusable_value(initialiser, value))
            {
                return Some(reused);
            }
        }
        None
    }

    /// The statements of the coerced top level, written over the run `run`
    /// of the stack as one list: the rows that remain, each rebound export
    /// inserted before its row, then the rebound exports of the tail. A
    /// flattened block loses its block statements. One step per row.
    pub(super) fn coerced_list(&mut self, run: Span) -> crate::bir::ListId {
        let mut out = std::mem::take(&mut self.scratch);
        debug_assert!(out.is_empty());
        let flattened = self.coercion.flattened;
        let mut inserted = 0;
        let mut blocks = std::mem::take(&mut self.coercion.path);
        blocks.clear();
        for index in 0..self.coercion.rows.len() {
            self.coercion.steps += 1;
            let Row { stmt, bits } = self.coercion.rows[index];
            while inserted < self.coercion.inserted.len()
                && self.coercion.inserted[inserted].0 as usize == index
            {
                out.push(self.coercion.inserted[inserted].1);
                inserted += 1;
            }
            if bits & (Row::REMOVED | Row::INSERTED) != 0 {
                continue;
            }
            if bits & Row::TAIL != 0 {
                out.push(stmt);
                continue;
            }
            if flattened {
                if self.arena.parents[stmt.index()].is_some() {
                    self.arena.detach(stmt);
                }
                if bits & Row::BLOCK != 0 {
                    blocks.push(stmt);
                    continue;
                }
            } else if bits & Row::NESTED != 0 {
                continue;
            }
            out.push(stmt);
        }
        // The statements of a dissolved block were detached above.
        for block in blocks.drain(..) {
            self.arena.release(block);
        }
        self.coercion.path = blocks;
        let list = self.arena.lists.push_iter(out.len(), out.iter().copied());
        self.statements.copied += out.len();
        self.statements.kill(run);
        out.clear();
        self.scratch = out;
        list
    }
}

#[cfg(test)]
mod tests {
    use super::{Arm, Resolved};
    use crate::ident::{Ident, IdentFlags};
    use crate::lambda::arena::{Lam, LamArena};
    use crate::lambda::lam_compat::LetKind;
    use crate::lambda::lam_compile::LambdaCompiler;
    use crate::lambda::lam_constant::Constant as C;
    use crate::lambda::lam_primitive::{Mutable, Primitive as P};
    use crate::lambda::{ApInfo, ApplyStatus, LamLoc, TagInfo};

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }
    fn exports(a: &mut LamArena, ids: &[Ident], values: &[Lam]) -> Lam {
        a.prim_raw(
            P::Pmakeblock(TagInfo::ModuleExport(ids.to_vec()), Mutable::Immutable),
            values,
            LamLoc::NONE,
        )
    }
    fn call(a: &mut LamArena, name: &str, stamp: i32) -> Lam {
        let callee = a.var(id(name, stamp));
        let unit = a.const_(C::JsUndefined { is_unit: true });
        a.apply_raw(
            callee,
            &[unit],
            ApInfo {
                status: ApplyStatus::InferFull,
                loc: LamLoc::NONE,
            },
        )
    }
    /// The oracle form: the same Lambda through the legacy pipeline and
    /// through the new lowering, both printed texts compared by the gate.
    /// Returns the legacy text after the passes.
    fn gate(a: LamArena, root: Lam) -> String {
        let mut compiler = LambdaCompiler::new();
        let (deps, check) =
            compiler.compile_deps_program_with_lower_check::<true>(a, root, Default::default());
        let check = check.unwrap();
        assert!(matches!(
            check,
            crate::bir::shadow::LowerCheck::Supported(_)
        ));
        crate::bir::shadow::check_lower(check, "Export.res", false).unwrap();
        crate::js_ir::print_deps_program_with_directives_and_options(
            &deps,
            None,
            &[],
            false,
            false,
            false,
        )
    }

    /// The rule form (BACKEND_LOWERING 8.3): the same Lambda, not simplified,
    /// through the legacy lowering with the legacy export code and through
    /// the new lowering without it. Both printed texts (before and after the
    /// JS passes) must be equal. Returns the arms the exports took and the
    /// text before the passes.
    fn rule(a: LamArena, root: Lam) -> (Vec<(Arm, Resolved)>, String) {
        let print = |deps: &crate::js_ir::arena::JsDepsProgram| {
            crate::js_ir::print_deps_program_with_directives_and_options(
                deps,
                None,
                &[],
                false,
                false,
                false,
            )
        };
        let input = crate::bir::bridge::import_for_lowering(&a, root).0.unwrap();
        let lowered = super::super::lower(input, None, false).unwrap();
        lowered
            .program
            .arena
            .validate(Some(lowered.program.root))
            .unwrap();
        let exported = crate::bir::bridge_j::export_js(&lowered.program).unwrap();
        let new_before = LambdaCompiler::bir_coerced_program(
            exported.program.arena,
            exported.program.block,
            lowered.coerced.exports.clone(),
            lowered.coerced.reservations.clone(),
        );
        let mut a = a;
        let mut compiler = LambdaCompiler::new();
        let before = compiler.bir_export_oracle(&mut a, root);
        let text = print(&before);
        assert_eq!(print(&new_before), text, "before the passes");
        let after = compiler.bir_passes_oracle(before);
        let new_after = compiler.bir_passes_oracle(new_before);
        assert_eq!(print(&new_after), print(&after), "after the passes");
        (lowered.coerced.arms, text)
    }
    fn function(a: &mut LamArena, stamp: i32) -> Lam {
        let param = id("arg", stamp);
        let body = a.var(param);
        a.function_(1, &[param], body, Default::default(), LamLoc::NONE)
    }
    fn member(a: &mut LamArena, module: &str, name: &str) -> Lam {
        let module = a.global_module(Ident::create_persistent(module));
        a.prim_raw(
            P::Pfield(0, crate::lambda::FieldDbgInfo::Module { name: name.into() }),
            &[module],
            LamLoc::NONE,
        )
    }
    fn call_with(a: &mut LamArena, name: &str, stamp: i32, arg: Lam) -> Lam {
        let callee = a.var(id(name, stamp));
        a.apply_raw(
            callee,
            &[arg],
            ApInfo {
                status: ApplyStatus::InferFull,
                loc: LamLoc::NONE,
            },
        )
    }

    #[test]
    fn a_plain_export_keeps_its_declaration() {
        let mut a = LamArena::new();
        let x = id("x", 10);
        let value = call(&mut a, "ext", 1);
        let read = a.var(x);
        let block = exports(&mut a, &[x], &[read]);
        let root = a.let_(LetKind::Strict, x, value, block);
        let (arms, text) = rule(a, root);
        assert_eq!(arms, [(Arm::DeclaredExport, Resolved::Chain(false))]);
        assert!(text.contains("let x = ext();"), "{text}");
    }

    #[test]
    fn an_export_used_internally_keeps_its_declaration() {
        let mut a = LamArena::new();
        let x = id("x", 10);
        let value = call(&mut a, "ext", 1);
        let read = a.var(x);
        let used = call_with(&mut a, "use", 2, read);
        let read = a.var(x);
        let block = exports(&mut a, &[x], &[read]);
        let tail = a.seq_raw(used, block);
        let root = a.let_(LetKind::Strict, x, value, tail);
        let (arms, text) = rule(a, root);
        assert_eq!(arms, [(Arm::DeclaredExport, Resolved::Chain(false))]);
        assert!(text.contains("use(x);"), "{text}");
    }

    #[test]
    fn an_export_of_a_same_name_local_is_renamed_to_it() {
        // `let x = ext()` under another stamp than the export `x`.
        let mut a = LamArena::new();
        let (local, export) = (id("x", 10), id("x", 20));
        let value = call(&mut a, "ext", 1);
        let read = a.var(local);
        let block = exports(&mut a, &[export], &[read]);
        let root = a.let_(LetKind::Strict, local, value, block);
        let (arms, _) = rule(a, root);
        assert_eq!(arms, [(Arm::DeclaredTarget, Resolved::Chain(false))]);
    }

    #[test]
    fn an_export_of_another_value_is_rebound() {
        for variable in [false, true] {
            let mut a = LamArena::new();
            let y = id("y", 10);
            let value = if variable {
                a.var(y)
            } else {
                call(&mut a, "ext", 1)
            };
            let block = exports(&mut a, &[id("x", 20)], &[value]);
            let root = if variable {
                let bound = call(&mut a, "ext", 1);
                a.let_(LetKind::Strict, y, bound, block)
            } else {
                block
            };
            let (arms, text) = rule(a, root);
            assert_eq!(arms, [(Arm::Rebound, Resolved::Chain(false))]);
            assert!(
                text.contains(if variable { "let x$1 = y;" } else { "let x$1 = ext();" }),
                "{text}"
            );
        }
    }

    #[test]
    fn an_export_of_a_literal_is_rebound() {
        let mut a = LamArena::new();
        let value = a.const_(C::Int { i: 42, comment: None });
        let root = exports(&mut a, &[id("answer", 10)], &[value]);
        let (arms, text) = rule(a, root);
        assert_eq!(arms, [(Arm::Rebound, Resolved::Chain(false))]);
        assert!(text.contains("let answer$1 = 42;"), "{text}");
    }

    /// `let f = function; let x = f; export x` where the export `x` has
    /// another stamp: the alias moves to the export tail and the references
    /// after it read `f`.
    fn alias_of_function(a: &mut LamArena, later: impl FnOnce(&mut LamArena, Ident) -> Option<Lam>) -> Lam {
        let (f, local, export) = (id("f", 5), id("x", 10), id("x", 20));
        let read = a.var(local);
        let block = exports(a, &[export], &[read]);
        let tail = match later(a, local) {
            Some(effect) => a.seq_raw(effect, block),
            None => block,
        };
        let alias = a.var(f);
        let inner = a.let_(LetKind::Alias, local, alias, tail);
        let function = function(a, 6);
        a.let_(LetKind::Strict, f, function, inner)
    }

    #[test]
    fn a_same_name_alias_moves_to_the_export_tail() {
        let mut a = LamArena::new();
        let root = alias_of_function(&mut a, |_, _| None);
        let (arms, text) = rule(a, root);
        assert_eq!(arms, [(Arm::MovedAlias, Resolved::Chain(false))]);
        assert!(text.contains("let x = f;"), "{text}");
    }

    #[test]
    fn a_moved_alias_is_replaced_where_it_is_called() {
        let mut a = LamArena::new();
        let root = alias_of_function(&mut a, |a, local| {
            let callee = a.var(local);
            let unit = a.const_(C::JsUndefined { is_unit: true });
            Some(a.apply_raw(
                callee,
                &[unit],
                ApInfo {
                    status: ApplyStatus::InferFull,
                    loc: LamLoc::NONE,
                },
            ))
        });
        let (arms, text) = rule(a, root);
        assert_eq!(arms, [(Arm::MovedAlias, Resolved::Chain(false))]);
        assert!(text.contains("f();"), "{text}");
        assert!(!text.contains("x();"), "{text}");
    }

    #[test]
    fn an_alias_used_as_an_argument_before_an_effect_stays() {
        let mut a = LamArena::new();
        let root = alias_of_function(&mut a, |a, local| {
            let read = a.var(local);
            Some(call_with(a, "use", 2, read))
        });
        let (arms, text) = rule(a, root);
        assert_eq!(arms, [(Arm::DeclaredTarget, Resolved::Chain(false))]);
        assert!(text.contains("let x$1 = f;") && text.contains("use(x$1);"), "{text}");
    }

    #[test]
    fn an_alias_used_before_its_declaration_row_or_in_a_later_function_stays() {
        // A later function literal that mentions the alias captures it.
        let mut a = LamArena::new();
        let root = alias_of_function(&mut a, |a, local| {
            let g = id("g", 30);
            let read = a.var(local);
            let param = id("arg", 31);
            let function = a.function_(1, &[param], read, Default::default(), LamLoc::NONE);
            let unit = a.const_(C::JsUndefined { is_unit: true });
            let bound = a.let_(LetKind::Strict, g, function, unit);
            Some(bound)
        });
        let (arms, _) = rule(a, root);
        assert_eq!(arms[0].0, Arm::DeclaredTarget);
    }

    #[test]
    fn an_alias_of_a_module_member_moves_unless_a_function_follows() {
        for followed in [false, true] {
            let mut a = LamArena::new();
            let (local, export) = (id("x", 10), id("x", 20));
            let read = a.var(local);
            let block = exports(&mut a, &[export], &[read]);
            let tail = if followed {
                let function = function(&mut a, 6);
                a.let_(LetKind::Strict, id("g", 30), function, block)
            } else {
                block
            };
            let value = member(&mut a, "Other", "x");
            let root = a.let_(LetKind::Alias, local, value, tail);
            let (arms, _) = rule(a, root);
            assert_eq!(
                arms[0].0,
                if followed { Arm::DeclaredTarget } else { Arm::MovedAlias }
            );
        }
    }

    #[test]
    fn an_export_shadowing_a_javascript_global() {
        let mut a = LamArena::new();
        let export = id("parseInt", 10);
        let global = a.var(Ident::create_persistent("parseInt"));
        let read = a.var(export);
        let block = exports(&mut a, &[export], &[read]);
        let root = a.let_(LetKind::Alias, export, global, block);
        let (arms, text) = rule(a, root);
        assert_eq!(arms, [(Arm::DeclaredExport, Resolved::Chain(false))]);
        assert!(text.contains("parseInt"), "{text}");
    }

    #[test]
    fn an_undefined_export_reuses_its_declaration() {
        let mut a = LamArena::new();
        let x = id("x", 10);
        let value = a.const_(C::JsUndefined { is_unit: false });
        let block = exports(&mut a, &[x], &[value]);
        let bound = a.const_(C::JsNull);
        let root = a.let_(LetKind::Strict, x, bound, block);
        let (arms, _) = rule(a, root);
        assert_eq!(arms, [(Arm::Undefined, Resolved::Chain(false))]);
    }

    #[test]
    fn an_export_of_a_member_reuses_a_same_name_binding() {
        // `let x = Other.f`, read by a later initialiser, so it cannot move.
        for own in [false, true] {
            let mut a = LamArena::new();
            let (local, export) = (id("x", 10), id("x", 20));
            let value = member(&mut a, "Other", "f");
            let block = exports(&mut a, &[if own { local } else { export }], &[value]);
            let read = a.var(local);
            let tail = a.let_(LetKind::Strict, id("y", 30), read, block);
            let bound = member(&mut a, "Other", "f");
            let root = a.let_(LetKind::Strict, local, bound, tail);
            let (arms, _) = rule(a, root);
            assert_eq!(arms[0].0, if own { Arm::KeptReused } else { Arm::Reused });
        }
    }

    #[test]
    fn an_export_of_a_member_moves_the_reused_binding() {
        let mut a = LamArena::new();
        let (local, export) = (id("x", 10), id("x", 20));
        let value = member(&mut a, "Other", "f");
        let block = exports(&mut a, &[export], &[value]);
        let bound = member(&mut a, "Other", "f");
        let root = a.let_(LetKind::Strict, local, bound, block);
        let (arms, _) = rule(a, root);
        assert_eq!(arms[0].0, Arm::MovedReused);
    }

    #[test]
    fn a_literal_export_is_inserted_before_equal_later_bindings() {
        // `let b = 1` is the end of the block and `b` is a later export.
        let mut a = LamArena::new();
        let (first, b) = (id("a", 10), id("b", 20));
        let value = a.const_(C::Int { i: 1, comment: None });
        let read = a.var(b);
        let block = exports(&mut a, &[first, b], &[value, read]);
        let bound = a.const_(C::Int { i: 1, comment: None });
        let root = a.let_(LetKind::Variable, b, bound, block);
        let (arms, text) = rule(a, root);
        assert_eq!(arms[0].0, Arm::Inserted);
        let (first, second) = (text.find("let a = 1;").unwrap(), text.find("let b = 1;").unwrap());
        assert!(first < second, "{text}");
    }

    #[test]
    fn resolution_keeps_a_function_export_with_a_second_same_name_root() {
        let mut a = LamArena::new();
        let (other, export) = (id("x", 10), id("x", 20));
        let read = a.var(export);
        let block = exports(&mut a, &[export], &[read]);
        let second = function(&mut a, 6);
        let inner = a.let_(LetKind::Strict, export, second, block);
        let first = function(&mut a, 7);
        let root = a.let_(LetKind::Strict, other, first, inner);
        let (arms, _) = rule(a, root);
        assert_eq!(arms, [(Arm::DeclaredExport, Resolved::KeptFunction)]);
    }

    /// `let x = <first>; let x' = <second>; export x' = undefined`: the fold
    /// keeps the declaration, the resolution decides.
    fn resolved(kind: LetKind, first: fn(&mut LamArena) -> Lam, second: fn(&mut LamArena, Ident) -> Lam) -> Vec<(Arm, Resolved)> {
        let mut a = LamArena::new();
        let (other, export) = (id("x", 10), id("x", 20));
        let value = a.const_(C::JsUndefined { is_unit: false });
        let block = exports(&mut a, &[export], &[value]);
        let second = second(&mut a, other);
        let inner = a.let_(kind, export, second, block);
        let first = first(&mut a);
        let root = a.let_(LetKind::Strict, other, first, inner);
        rule(a, root).0
    }

    #[test]
    fn resolution_follows_a_same_name_self_alias() {
        let arms = resolved(LetKind::Alias, |a| call(a, "ext", 1), |a, other| a.var(other));
        assert_eq!(arms, [(Arm::Undefined, Resolved::SelfAlias)]);
    }

    #[test]
    fn resolution_reuses_a_same_name_binding_with_the_same_initialiser() {
        let arms = resolved(
            LetKind::Strict,
            |a| member(a, "Other", "f"),
            |a, _| member(a, "Other", "f"),
        );
        assert_eq!(arms, [(Arm::Undefined, Resolved::ReusableDeclared)]);
    }

    #[test]
    fn resolution_follows_the_alias_chain_through_a_variable_binding() {
        let arms = resolved(LetKind::Variable, |a| call(a, "ext", 1), |a, other| a.var(other));
        assert_eq!(arms, [(Arm::Undefined, Resolved::Chain(true))]);
    }

    #[test]
    fn resolution_leaves_an_export_without_alias() {
        let arms = resolved(LetKind::Strict, |a| call(a, "ext", 1), |a, _| call(a, "ext", 2));
        assert_eq!(arms, [(Arm::Undefined, Resolved::Chain(false))]);
    }

    #[test]
    fn a_finished_top_level_declares_its_undeclared_exports() {
        let mut a = LamArena::new();
        let (x, y) = (id("x", 10), id("y", 11));
        let payload = a.const_(C::JsNull);
        let raised = a.prim_raw(P::Praise, &[payload], LamLoc::NONE);
        let (rx, ry) = (a.var(x), a.var(y));
        let block = exports(&mut a, &[x, y], &[rx, ry]);
        let bound = call(&mut a, "ext", 1);
        let inner = a.let_(LetKind::Strict, y, raised, block);
        let root = a.let_(LetKind::Strict, x, bound, inner);
        let (arms, text) = rule(a, root);
        assert_eq!(arms.len(), 2);
        assert!(text.contains("let y;"), "{text}");
    }

    #[test]
    fn a_plain_export_is_extracted() {
        let mut a = LamArena::new();
        let x = id("x", 10);
        let value = call(&mut a, "ext", 1);
        let read = a.var(x);
        let block = exports(&mut a, &[x], &[read]);
        let root = a.let_(LetKind::Strict, x, value, block);
        let text = gate(a, root);
        assert!(text.contains("let x = ext();"), "{text}");
        assert!(text.contains("x,"), "{text}");
    }

    #[test]
    fn an_export_of_a_value_that_is_not_a_variable_is_extracted() {
        let mut a = LamArena::new();
        let value = a.const_(C::Int { i: 42, comment: None });
        let root = exports(&mut a, &[id("answer", 10)], &[value]);
        let text = gate(a, root);
        assert!(text.contains("let answer = 42;"), "{text}");
    }

    #[test]
    fn a_unit_without_exports_has_no_export_block() {
        let mut a = LamArena::new();
        let root = exports(&mut a, &[], &[]);
        gate(a, root);
        let mut a = LamArena::new();
        let root = a.const_(C::JsUndefined { is_unit: true });
        gate(a, root);
    }

    #[test]
    fn a_unit_whose_only_statement_is_an_effect() {
        let mut a = LamArena::new();
        let root = call(&mut a, "ext", 1);
        let text = gate(a, root);
        assert!(text.contains("ext();"), "{text}");
    }

    #[test]
    fn the_heads_of_a_comma_before_the_export_block_are_effects() {
        let mut a = LamArena::new();
        let first = call(&mut a, "first", 1);
        let second = call(&mut a, "second", 2);
        let value = a.const_(C::JsTrue);
        let block = exports(&mut a, &[id("flag", 10)], &[value]);
        let tail = a.seq_raw(second, block);
        let root = a.seq_raw(first, tail);
        let text = gate(a, root);
        let (first, second) = (text.find("first();").unwrap(), text.find("second();").unwrap());
        assert!(first < second, "{text}");
        assert!(text.contains("let flag = true;"), "{text}");
    }

    #[test]
    fn a_finished_unit_exports_undefined_values() {
        let mut a = LamArena::new();
        let x = id("x", 10);
        let payload = a.const_(C::JsNull);
        let raised = a.prim_raw(P::Praise, &[payload], LamLoc::NONE);
        let read = a.var(x);
        let block = exports(&mut a, &[x], &[read]);
        let root = a.let_(LetKind::Strict, x, raised, block);
        let text = gate(a, root);
        assert!(text.contains("throw null;"), "{text}");
        assert!(text.contains("let x;"), "{text}");
    }

    #[test]
    fn row_and_fact_sizes() {
        use std::mem::size_of;
        assert_eq!(size_of::<super::Row>(), 8);
        assert_eq!(size_of::<crate::bir::lower::scope::Site>(), 8);
        // Passed down the fold.
        assert_eq!(size_of::<super::Init>(), 12);
        assert_eq!(size_of::<super::Replacement>(), 8);
        assert_eq!(size_of::<super::Kind>(), 1);
        assert_eq!(size_of::<super::Mentions>(), 1);
    }

    /// `let x0 = ext(); ... let x9999 = ext(); export x0, ..., x9999`.
    #[test]
    fn ten_thousand_rows_with_ten_thousand_exports_are_coerced_in_linear_steps() {
        const N: usize = 10_000;
        let mut a = LamArena::new();
        let ids: Vec<Ident> = (0..N).map(|i| id(&format!("x{i}"), 100 + i as i32)).collect();
        let values: Vec<Lam> = ids.iter().map(|&x| a.var(x)).collect();
        let mut root = exports(&mut a, &ids, &values);
        for &x in ids.iter().rev() {
            let value = call(&mut a, "ext", 1);
            root = a.let_(LetKind::Strict, x, value, root);
        }
        let input = crate::bir::bridge::import_for_lowering(&a, root).0.unwrap();
        let lowered = super::super::lower(input, None, false).unwrap();
        assert_eq!(lowered.coerced.exports, ids);
        assert!(lowered.coerced.arms.iter().all(|arm| arm.0 == Arm::DeclaredExport));
        // The bound of `coerce_exports` and `coerced_list` for this shape:
        // two steps per row (written, copied) and eight per export (its
        // table entry, its turn in the fold and in the resolution, one link
        // of each of the four alias chains it reads and one declaration of
        // its name). No site is read: an export of its own variable asks
        // about no reference.
        println!("10,000 rows, 10,000 exports: {} steps", lowered.coerced.steps);
        assert!(lowered.coerced.steps <= 2 * N + 8 * N, "{}", lowered.coerced.steps);
        assert_eq!(lowered.coerced.site_visits, 0);
    }

    /// `let f = function; let x = f; x(); ... x(); export x` (10,000 calls).
    fn alias_with_references(a: &mut LamArena, n: usize, argument: bool) -> Lam {
        let (f, local, export) = (id("f", 5), id("x", 10), id("x", 20));
        let read = a.var(local);
        let mut tail = exports(a, &[export], &[read]);
        for _ in 0..n {
            let read = a.var(local);
            let effect = if argument {
                call_with(a, "use", 2, read)
            } else {
                let unit = a.const_(C::JsUndefined { is_unit: true });
                a.apply_raw(
                    read,
                    &[unit],
                    ApInfo {
                        status: ApplyStatus::InferFull,
                        loc: LamLoc::NONE,
                    },
                )
            };
            tail = a.seq_raw(effect, tail);
        }
        let alias = a.var(f);
        let inner = a.let_(LetKind::Alias, local, alias, tail);
        let function = function(a, 6);
        a.let_(LetKind::Strict, f, function, inner)
    }

    #[test]
    fn ten_thousand_references_to_a_moved_alias_are_each_visited_once() {
        const N: usize = 10_000;
        let mut a = LamArena::new();
        let root = alias_with_references(&mut a, N, false);
        let input = crate::bir::bridge::import_for_lowering(&a, root).0.unwrap();
        let lowered = super::super::lower(input, None, false).unwrap();
        lowered
            .program
            .arena
            .validate(Some(lowered.program.root))
            .unwrap();
        assert_eq!(lowered.coerced.arms, [(Arm::MovedAlias, Resolved::Chain(false))]);
        // The N calls and the export value are the sites of the alias, read
        // once by the one pass that decides and collects; the function's
        // one reference (the alias's initialiser) is read by the two
        // questions asked about the function.
        assert_eq!(lowered.coerced.site_visits, N + 1 + 2);
        // Per reference: the site, the call above it (entered once), and
        // the replacement. Per row: written, entered in the table dense by
        // node, and copied.
        println!("10,000 references to one alias: {} steps", lowered.coerced.steps);
        assert!(lowered.coerced.steps <= 3 * (N + 1) + 3 * (N + 2) + 32, "{}", lowered.coerced.steps);
    }

    #[test]
    fn rows_and_references_are_read_without_allocation_once_the_tables_are_warm() {
        use super::*;
        const N: usize = 10_000;
        let mut a = LamArena::new();
        // Used as an argument before an effect: the alias stays, so the
        // pass can be repeated on the same tree.
        let root = alias_with_references(&mut a, N, true);
        let input = crate::bir::bridge::import_for_lowering(&a, root).0.unwrap().into_imported();
        let root = input.root;
        let mut state = State::new(input);
        let probed = state.probe(Cx::value(), root).unwrap();
        let out = state.realize(Cx::value(), probed);
        let exports = state.extract_exports(out.value, out.finished).unwrap();
        let run = state.statements.since(Span { start: out.stmts.start, len: 0 });
        let mut vars = Vec::new();
        state.export_variables(&exports, &mut vars);
        let value = state.coercion.values[0];
        // Warm: the tables get their capacity.
        state.build_rows(run, &vars);
        assert_eq!(state.coercion.rows.len(), N + 2);
        assert!(state.move_alias_to_tail(vars[0], value).is_none());
        let visits = state.coercion.site_visits;
        let allocations = allocation_counter::measure(|| {
            state.build_rows(run, &vars);
            assert!(state.move_alias_to_tail(vars[0], value).is_none());
        });
        assert!(state.coercion.site_visits - visits >= N);
        assert_eq!(allocations.count_total, 0, "{allocations:?}");
        println!(
            "10,002 rows and 10,001 references read again: {} heap allocations",
            allocations.count_total
        );
    }
}
