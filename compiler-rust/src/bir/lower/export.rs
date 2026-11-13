//! T4a (THREE_TREES 11.4, "T4a as built"): the unit's exports. The last
//! value of the top level is read for the export block where the lowering
//! completes it, and the exports are coerced on top-level rows:
//! O:209 extract_toplevel_exports and C:1099
//! coerce_toplevel_exports_with_name_reservations with the tail-move helpers
//! of js_shake.rs (S).
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
    /// Rebound exports after the top level, in fold order.
    rebound: Vec<NodeId>,
    /// The block was flattened: a moved alias did it (S:160 substitute_after).
    flattened: bool,
    /// The last row plus one with the bit, among the statements of the
    /// flattened block.
    last_function: u32,
    last_plain: u32,
    /// The last row plus one with a top-level effect; `u32::MAX` unread.
    last_effect: u32,
    /// Rows, exports, alias-chain links, sites and ancestors visited.
    pub(super) steps: usize,
}

/// The exports of a unit as the lowering hands them over.
pub(crate) struct Coerced {
    /// The exported identifiers after coercion, in export order.
    pub exports: Vec<Ident>,
    /// The original export identifiers whose name a selected local shadows.
    pub reservations: Vec<Ident>,
}

impl State {
    /// O:209 extract_toplevel_exports and the finished case of
    /// lam_compile_main.ml:390-395. Reads the unit's last value: an export
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
        t.rebound.clear();
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
        if bits & Row::REMOVED != 0 {
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
                if bits & (Row::BLOCK | Row::REMOVED) == 0 && self.has_toplevel_effect(row) {
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
                if row.bits & Row::REMOVED == 0 {
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
    /// replacement_resolves_to_recursive_function). Cost: one step per site
    /// of the variable, released ones included, plus `row_of`.
    fn mentions(&mut self, var: VarId, index: u32) -> Mentions {
        let mut found = Mentions::default();
        let Some(scope) = &self.arena.js_scope else {
            unreachable!("the lowering arena records sites")
        };
        let mut at = scope.site_heads[var.index()];
        while at != 0 {
            self.coercion.steps += 1;
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
            && self.mentions(var, row).has(Mentions::OWN)
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
    /// replace every reference to `target` in a later row by a copy of the
    /// replacement. Cost: one step and one copy per site of `target`. The
    /// block is flattened from here on.
    fn substitute_after(&mut self, index: u32, target: VarId, replacement: Replacement) {
        let mut at = self.arena.js_scope.as_ref().expect("sites").site_heads[target.index()];
        while at != 0 {
            self.coercion.steps += 1;
            let site = self.arena.js_scope.as_ref().expect("sites").sites[at as usize - 1];
            at = site.next;
            if site.node == NodeId(u32::MAX) {
                continue;
            }
            let Some(parent) = self.arena.parents[site.node.index()] else {
                continue;
            };
            let place = self.row_of(parent);
            if place == 1 || (place >> 1) - 1 <= index {
                continue;
            }
            let copy = self.copy_replacement(replacement);
            self.arena.replace(site.node, copy);
        }
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

    /// B:1420 define, for an export: `let export = value`. When the export
    /// variable is declared already, the declaration binds a copy that
    /// prints as the export. Constant.
    fn define(&mut self, var: VarId, value: NodeId, kind: LetKind) -> NodeId {
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
            View::SDecl {
                var,
                value: Some(value),
            },
            kind as u16 | ((crate::js_ir::op::UsedStats::default() as u16) << 2),
        );
        self.built(stmt)
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
        let uses = self.mentions(target, index);
        let later_initialiser = uses.has(Mentions::LATER_INITIALISER);
        let prefer_materialized_root = match self.materialized_root(init, true) {
            Some(root) if root != target => {
                later_initialiser || self.mentions(root, index).has(Mentions::LATER)
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
        self.substitute_after(index, target, replacement);
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
        let uses = self.mentions(reused, index);
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
        self.substitute_after(index, reused, replacement);
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
        let stmt = self.define(var, value, LetKind::Strict);
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
    /// visited reference and its statement.
    pub(super) fn coerce_exports(&mut self, run: Span, idents: Vec<Ident>, finished: Finished) -> Coerced {
        let mut exports = Vec::with_capacity(idents.len());
        self.export_variables(&idents, &mut exports);
        self.build_rows(run, &exports);
        let block_ended = finished == Finished::True;
        let mut selected = Vec::with_capacity(idents.len());
        let mut reservations = Vec::new();
        for index in 0..exports.len() as u32 {
            self.coercion.steps += 1;
            let export = exports[index as usize];
            let ident = idents[index as usize];
            let value = self.coercion.values[index as usize];
            let value_var = match self.arena.view(value) {
                View::Var { var } => Some(self.origin(var)),
                _ => None,
            };
            let exact_self_export = value_var == Some(export);
            // lam_coercion.ml:99-111: an export of its own identifier
            // changes the export list only.
            if !exact_self_export {
                if let Some((replacement, property)) = self.move_alias_to_tail(export, value) {
                    let late = self.copy_replacement(replacement);
                    let target = value_var.expect("a moved alias is a variable");
                    let row = self.declaration_row_removed(target);
                    self.release_row(row);
                    self.arena.release(value);
                    let stmt = self.define(export, late, property);
                    self.coercion.rebound.push(stmt);
                    selected.push(ident);
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
                        }
                        selected.push(self.ident(chosen));
                        self.arena.release(value);
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
                        }
                        selected.push(self.ident(chosen));
                        self.arena.release(value);
                        continue;
                    }
                }
            }
            if matches!(self.arena.view(value), View::JUndefined)
                && ((self.declared(export) && self.can_reuse_undefined(export)) || block_ended)
            {
                selected.push(ident);
                self.arena.release(value);
                continue;
            }
            if self.reusable_candidate(value) {
                if let Some((replacement, property)) = self.move_reused_to_tail(index, value) {
                    let late = self.copy_replacement(replacement);
                    let row = self.reused_row_removed(index);
                    self.release_row(row);
                    self.arena.release(value);
                    let stmt = self.define(export, late, property);
                    self.coercion.rebound.push(stmt);
                    selected.push(ident);
                    continue;
                }
                if let Some(row) = self.reused_binding(index, value) {
                    let (reused, _, property) = self.declared_by(row);
                    // S:599 keeps_declared_same_name_reusable_export_binding.
                    if reused == export && property != LetKind::Variable {
                        selected.push(ident);
                        self.arena.release(value);
                        continue;
                    }
                }
                // O:295 reusable_same_name_export_binding.
                if let Some(reused) = self.reusable_binding(index, export, value) {
                    selected.push(self.ident(reused));
                    self.arena.release(value);
                    continue;
                }
            }
            if self.insert_before_equivalent(index, export, value, &exports) {
                selected.push(ident);
                continue;
            }
            // lam_coercion.ml:140-156: `Ident.rename` of the export.
            let rebound = self.fresh_variable(self.arena.vars.name(export).as_str());
            self.sync_tables();
            reservations.push(ident);
            let property = if value_var.is_some() {
                LetKind::Alias
            } else {
                LetKind::Strict
            };
            selected.push(self.ident(rebound));
            let stmt = self.define(rebound, value, property);
            self.coercion.rebound.push(stmt);
        }
        Coerced {
            exports: selected,
            reservations,
        }
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
            if bits & Row::REMOVED != 0 {
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
        out.extend_from_slice(&self.coercion.rebound);
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
}
