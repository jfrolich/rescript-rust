- Replace per-construct check-mode lowering storage with typed pools and retained scratch, including mixed switches and cross-module inlining. Pin complete-unit allocation counts across two source sizes and document attribution, shared callers, parity and instruction measurements without claiming a wall-time speedup. [#225](https://github.com/jfrolich/rescript-rust/pull/225)

Keep the pooled untagged planner exclusive to BIR; restore the legacy planner
and its callers unchanged. The CI-profile default instruction gate is within
+0.02%, with the check-mode reduction retained; full raw counts are documented
in `compiler-rust/docs/LOWERING_ALLOCATION_SCALING.md`.
