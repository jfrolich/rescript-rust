# Parser Strict Side Tables Progress

> Living document. Update after each completed migration chunk.

## Status

Current status: not started (planning complete).

## Baseline Snapshot (February 17, 2026)

1. Inline parser AST attribute fields (`...attributes`): 13
2. Additional inline attribute carriers (`TypeArg`, `RowField::Rtag`, `ObjectField::Otag`, `Pstr_eval`, `Pstr_extension`, `Psig_extension`): 6
3. `stash_*` call sites in `compiler-rust/src`: 119
4. `pending_*` infrastructure centered in `parse_arena.rs`

Validation baseline:

1. `cargo check --manifest-path compiler-rust/Cargo.toml -q`: pass
2. `scripts/test_parser_ast_parity.sh`: pass (full parity)
3. Single-thread in-process benchmark (`benchmark_cold_repeat`): pass

## Milestones

- [ ] Phase 0 inventory and guardrails
- [ ] Phase 1 strict APIs for existing arena kinds
- [ ] Phase 2 remove stash/pending from existing arena kinds
- [ ] Phase 3 declaration/module node attribute side tables
- [ ] Phase 4 `TypeArg` / `RowField` / `ObjectField` migration
- [ ] Phase 5 structure/signature eval/extension migration
- [ ] Phase 6 delete legacy stash/pending infrastructure
- [ ] Phase 7 final validation and performance check

## Change Log

### February 17, 2026

1. Created project directory and initial docs:
   - `PLAN.md`
   - `INVENTORY.md`
   - `PROGRESS.md`
2. Recorded concrete baseline counts and validation status.

