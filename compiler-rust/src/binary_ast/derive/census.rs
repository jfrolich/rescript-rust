//! Opt-in, module-owned accounting for derived code. No global mutable census.
use std::path::PathBuf;
use std::time::Instant;
use serde::Serialize;
use crate::parse_arena::ParseArena;
use crate::parser::ast::{StructureItem, StructureItemDesc};
use crate::binary_ast::ast_iter::{self, AstIter};

/// Exact item attribution or an explicitly labelled whole-module estimate.
#[derive(Clone, Debug, Default, Serialize)]
pub struct Pair {
    /// Nanoseconds charged to derived items.
    pub derived: u64,
    /// Nanoseconds charged to other items.
    pub other: u64,
    /// Whether attribution is proportional to syntax-node counts.
    pub estimated: bool,
}
impl Pair {
    /// O(1): add one elapsed interval to one side; no allocation.
    pub fn add(&mut self, derived: bool, ns: u64) {
        if derived { self.derived += ns; } else { self.other += ns; }
    }
    /// O(1): sum both sides.
    pub fn total(&self) -> u64 { self.derived + self.other }
    /// O(1): partition an interval using integer arithmetic, preserving its sum.
    fn estimate(ns: u64, nodes: [u64; 2]) -> Self {
        let derived = if nodes[0] + nodes[1] == 0 { 0 } else {
            ((ns as u128 * nodes[0] as u128) / (nodes[0] + nodes[1]) as u128) as u64
        };
        Self { derived, other: ns - derived, estimated: true }
    }
}

/// One record per implementation compilation, carried across worker boundaries.
#[derive(Clone, Debug, Serialize)]
pub struct Census {
    /// Stable schema version.
    pub version: u32,
    /// Source file, as supplied to the compiler.
    pub module: String,
    /// Derived and other top-level bindings, including nested structures.
    pub bindings: [u64; 2],
    /// Derived and other syntax nodes (expression/pattern/type/module/item occurrences).
    pub syntax_nodes: [u64; 2],
    /// Source parsing/dependencies outside the measured frontend, charged to other.
    pub parse_other: Pair,
    /// Generation, measured at the derive seam.
    pub generation: Pair,
    /// Frontend work excluding generation and the census observer.
    pub frontend: Pair,
    /// Item-exclusive type checking; residual module overhead is charged to other.
    pub typecheck: Pair,
    /// Translation of value groups to raw Lambda.
    pub conversion: Pair,
    /// Remaining Lambda lowering, including conversion overhead outside value groups.
    pub lambda_lowering: Pair,
    /// Module-wide Lambda optimization.
    pub lambda_passes: Pair,
    /// Module-wide JavaScript lowering.
    pub lowering: Pair,
    /// Module-wide JavaScript printing.
    pub printing: Pair,
    /// Environment setup and signature publication are not derived-body work.
    pub environment: Pair,
    /// Signature publication.
    pub signature: Pair,
    /// GenType work.
    pub gentype: Pair,
    /// Printed bytes, estimated by syntax-node share.
    pub js_bytes: Pair,
    /// Printed lines, estimated by syntax-node share.
    pub js_lines: Pair,
    /// Derived/other deltas: fresh variables, top-level unifications, instance
    /// copied nodes, lazy environment hits+misses. Null unless counters are
    /// enabled and RAYON_NUM_THREADS=1; counters are process-global.
    pub checker_counters: Option<[[u64; 4]; 2]>,
    /// Base shape class per generated binding, in generation order.
    pub shape_classes: Vec<&'static str>,
    /// Body node occurrences per binding.
    pub shape_nodes: Vec<u64>,
    /// Orthogonal parameterisation flag per binding.
    pub shape_parameterised: Vec<bool>,
    /// Orthogonal recursive-group flag per binding.
    pub shape_recursive: Vec<bool>,
    /// Canonical structural bytes per binding; null means unsupported syntax.
    pub templates: Vec<Option<Vec<u8>>>,
    #[serde(skip)]
    pub(crate) observer_ns: u64,
    #[serde(skip)]
    pub(crate) output: PathBuf,
    #[serde(skip)]
    pub(crate) typed_groups: Vec<u64>,
}
impl Census {
    /// O(filename + path length): allocate one record per compilation, never per node.
    pub fn new(path: &std::path::Path, module: &str) -> Self {
        Self { version: 1, module: module.into(), output: path.into(), bindings: [0; 2],
            syntax_nodes: [0; 2], parse_other: Pair::default(), generation: Pair::default(), frontend: Pair::default(),
            typecheck: Pair::default(), conversion: Pair::default(), lambda_lowering: Pair::default(),
            lambda_passes: Pair::default(), lowering: Pair::default(), printing: Pair::default(),
            environment: Pair::default(), signature: Pair::default(), gentype: Pair::default(),
            js_bytes: Pair::default(), js_lines: Pair::default(), checker_counters: (crate::perf_counters::enabled()
                && std::env::var("RAYON_NUM_THREADS").as_deref() == Ok("1"))
                .then_some([[0; 4]; 2]),
            typed_groups: Vec::new(), shape_classes: Vec::new(), shape_nodes: Vec::new(),
            shape_parameterised: Vec::new(), shape_recursive: Vec::new(), templates: Vec::new(), observer_ns: 0 }
    }
    /// O(new words) on growth, O(1) otherwise; one bit per typed binding-pool slot.
    pub fn mark_typed_group(&mut self, start: u32) {
        let i = start as usize;
        self.typed_groups.resize(self.typed_groups.len().max(i / 64 + 1), 0);
        self.typed_groups[i / 64] |= 1 << (i % 64);
    }
    /// O(1): a bounds check and one bitmap read, with no synchronization.
    pub fn typed_group(&self, start: u32) -> bool {
        let i = start as usize;
        self.typed_groups.get(i / 64).is_some_and(|w| w & (1 << (i % 64)) != 0)
    }
    /// O(1): snapshot only the already enabled, single-worker counters.
    pub fn counter_snapshot(&self) -> Option<([u64; 4], [u64; 4])> {
        self.checker_counters.map(|counts| (crate::perf_counters::derived_snapshot(),
            std::array::from_fn(|i| counts[0][i] + counts[1][i])))
    }
    /// O(1): subtract nested items so every counter increment is charged once.
    pub fn account_counters(&mut self, derived: bool, before: Option<([u64; 4], [u64; 4])>) {
        if let (Some(counts), Some((before, charged))) = (&mut self.checker_counters, before) {
            let now = crate::perf_counters::derived_snapshot();
            for i in 0..4 {
                let children = counts[0][i] + counts[1][i] - charged[i];
                counts[usize::from(!derived)][i] += now[i].saturating_sub(before[i]).saturating_sub(children);
            }
        }
    }
    /// O(1): use exactly the existing phase-timer intervals; no new timers here.
    pub fn account_pre_js(&mut self, s: crate::timing::PhaseTimingSnapshot) {
        self.typecheck.other += nanos(s.typecheck).saturating_sub(self.typecheck.total());
        self.lambda_lowering = Pair::estimate(nanos(s.lambda).saturating_sub(self.conversion.total()), self.syntax_nodes);
        self.environment.other += nanos(s.env_setup);
        self.signature.other += nanos(s.signature_publish);
        self.gentype.other += nanos(s.gentype);
    }
    /// O(1): partition module-wide backend times by syntax weight, preserving totals.
    pub fn account_js(&mut self, s: crate::timing::PhaseTimingSnapshot, print_ns: u64) {
        self.lambda_passes = Pair::estimate(nanos(s.lambda_optimization), self.syntax_nodes);
        self.printing = Pair::estimate(print_ns, self.syntax_nodes);
        self.lowering = Pair::estimate(nanos(s.codegen).saturating_sub(print_ns), self.syntax_nodes);
    }
    /// O(output bytes): count bytes/lines without allocating per line, then append
    /// one JSON line under a process-wide output lock (one acquisition per module).
    pub fn finish(&mut self, outputs: impl Iterator<Item = impl AsRef<str>>) -> std::io::Result<()> {
        use std::io::Write;
        let (mut bytes, mut lines) = (0, 0);
        for text in outputs {
            let text = text.as_ref();
            bytes += text.len() as u64;
            lines += text.lines().count() as u64;
        }
        self.js_bytes = Pair::estimate(bytes, self.syntax_nodes);
        self.js_lines = Pair::estimate(lines, self.syntax_nodes);
        let mut encoded = serde_json::to_vec(self)?;
        encoded.push(b'\n');
        static OUTPUT: std::sync::Mutex<()> = std::sync::Mutex::new(());
        let _guard = OUTPUT.lock().unwrap_or_else(|e| e.into_inner());
        std::fs::OpenOptions::new().create(true).append(true).open(&self.output)?.write_all(&encoded)
    }
    /// O(node occurrences), one read-only observer pass. No per-node allocations;
    /// a nested structure changes attribution without charging its body twice.
    pub fn observe(&mut self, arena: &ParseArena, items: &[StructureItem]) {
        let mut totals = CountTotals::default();
        ast_iter::walk_structure(&mut Counts { totals: &mut totals, side: 1 }, arena, items);
        self.syntax_nodes = totals.nodes;
        self.bindings = totals.bindings;
    }
    /// O(1): retain the parse phase total after subtracting its frontend children.
    pub fn account_parse(&mut self, total: u64) {
        self.parse_other.other = total.saturating_sub(self.frontend.total() + self.generation.total());
    }
    /// O(node occurrences): count signature syntax; signatures currently have no
    /// structure provenance and are reported entirely on the other side.
    pub fn observe_signature(&mut self, arena: &ParseArena, items: &[crate::parser::ast::SignatureItem]) {
        let mut totals = CountTotals::default();
        ast_iter::walk_signature(&mut Counts { totals: &mut totals, side: 1 }, arena, items);
        self.syntax_nodes = totals.nodes;
    }
    /// O(1): remove measured generation from the frontend interval and partition
    /// the remaining module-wide walk time by node count.
    pub fn account_frontend(&mut self, elapsed: u64) {
        self.frontend = Pair::estimate(elapsed.saturating_sub(self.generation.total() + self.observer_ns), self.syntax_nodes);
    }
}

/// O(1), saturating duration conversion.
pub fn nanos(d: std::time::Duration) -> u64 { d.as_nanos().min(u64::MAX as u128) as u64 }
/// O(1): no clock read when disabled.
pub fn start(enabled: bool) -> Option<Instant> { enabled.then(Instant::now) }

#[derive(Default)]
struct CountTotals { nodes: [u64; 2], bindings: [u64; 2] }
struct Counts<'a> { totals: &'a mut CountTotals, side: usize }
impl AstIter for Counts<'_> {
    fn structure_item(&mut self, arena: &ParseArena, item: &StructureItem) {
        let previous = self.side;
        self.side = usize::from(!super::is_derived_item(item, arena));
        self.totals.nodes[self.side] += 1;
        if let StructureItemDesc::Pstr_value((_, group)) = item.pstr_desc {
            self.totals.bindings[self.side] += group.len() as u64;
        }
        ast_iter::walk_structure_item(self, arena, item);
        self.side = previous;
    }
    fn expr(&mut self, a: &ParseArena, i: crate::parse_arena::ExprIdx) {
        self.totals.nodes[self.side] += 1; ast_iter::walk_expr(self, a, i);
    }
    fn pat(&mut self, a: &ParseArena, i: crate::parse_arena::PatIdx) {
        self.totals.nodes[self.side] += 1; ast_iter::walk_pat(self, a, i);
    }
    fn typ(&mut self, a: &ParseArena, i: crate::parse_arena::CoreTypeIdx) {
        self.totals.nodes[self.side] += 1; ast_iter::walk_typ(self, a, i);
    }
    fn module_expr(&mut self, a: &ParseArena, i: crate::parse_arena::ModExprIdx) {
        self.totals.nodes[self.side] += 1; ast_iter::walk_module_expr(self, a, i);
    }
    fn module_type(&mut self, a: &ParseArena, i: crate::parse_arena::ModTypeIdx) {
        self.totals.nodes[self.side] += 1; ast_iter::walk_module_type(self, a, i);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn observer_visits_ten_thousand_array_elements_once() {
        assert_eq!(std::mem::size_of::<Counts<'_>>(), 16);
        let source = format!("let xs = [{}]", vec!["0"; 10_000].join(","));
        let mut parser = crate::parser::Parser::new("count.res", &source);
        let items = crate::parser::module::parse_structure(&mut parser);
        assert!(!parser.has_errors());
        let mut census = Census::new(std::path::Path::new("unused"), "count.res");
        census.observe(parser.arena(), &items);
        // 10,000 constant occurrences + array + variable pattern + structure item.
        assert_eq!(census.syntax_nodes, [0, 10_003]);
        assert_eq!(census.bindings, [0, 1]);
    }

    #[test]
    fn splits_preserve_totals_at_ten_thousand_sizes() {
        for n in 0..10_000 {
            let pair = Pair::estimate(n, [13, 29]);
            assert_eq!(pair.total(), n);
        }
        assert_eq!(Pair::estimate(31, [0, 0]).other, 31);
    }
}
