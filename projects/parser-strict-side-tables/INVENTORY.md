# Parser Strict Side Tables Inventory

Snapshot date: February 17, 2026

This inventory captures the starting state before strict migration.

## 1. Remaining Inline Attribute Carriers in `parser/ast.rs`

## A. Struct fields named `...attributes`

1. `ValueBinding.pvb_attributes`
2. `ValueDescription.pval_attributes`
3. `TypeDeclaration.ptype_attributes`
4. `ConstructorDeclaration.pcd_attributes`
5. `LabelDeclaration.pld_attributes`
6. `TypeExtension.ptyext_attributes`
7. `ExtensionConstructor.pext_attributes`
8. `ModuleBinding.pmb_attributes`
9. `ModuleDeclaration.pmd_attributes`
10. `ModuleTypeDeclaration.pmtd_attributes`
11. `OpenDescription.popen_attributes`
12. `IncludeDescription.pincl_attributes`
13. `IncludeDeclaration.pincl_attributes`

## B. Non-`...attributes` inline carriers

1. `TypeArg.attrs`
2. `RowField::Rtag(..., Attributes, ..., ...)`
3. `ObjectField::Otag(..., Attributes, ...)`
4. `StructureItemDesc::Pstr_eval(Box<(ExprIdx, Attributes)>)`
5. `StructureItemDesc::Pstr_extension(Box<(Extension, Attributes)>)`
6. `SignatureItemDesc::Psig_extension(Box<(Extension, Attributes)>)`

## 2. Stash/Pending Baseline

Code scan (`rg "stash_[a-z_]+\\(" compiler-rust/src`):

1. Total `stash_*` call sites: `119`
2. Top files:
   - `compiler-rust/src/parser/expr.rs`: 30
   - `compiler-rust/src/parse_arena.rs`: 26
   - `compiler-rust/src/binary_ast/ppx.rs`: 18
   - `compiler-rust/src/parser/jsx_ppx.rs`: 12
   - `compiler-rust/src/parser/let_unwrap_ppx.rs`: 8
   - `compiler-rust/src/binary_ast/mapper_from0.rs`: 8
   - `compiler-rust/src/parser/typ.rs`: 6
   - `compiler-rust/src/parser/module.rs`: 5
   - `compiler-rust/src/binary_ast/spice_ppx.rs`: 5
   - `compiler-rust/src/parser/pattern.rs`: 1

Code scan (`rg "pending_[a-z_]+" compiler-rust/src`):

1. `pending_*` occurrences in `parse_arena.rs`: 79
2. Non-parser false-positive naming in `parser/formatter.rs`: 2 (`pending_count`)

## 3. Existing Side Tables Already In Place

The following owner-index side tables already exist in `ParseArena`:

1. Expression sparse fields:
   - fun default
   - case guards
   - construct arg
   - variant arg
   - record spread
   - if-else branch
   - coerce from-type
2. Attributes for arena-indexed kinds:
   - expression
   - pattern
   - core type
   - module expression
   - module type

These still rely on pending/stash compatibility flow and need strict conversion.

## 4. Validation Baseline

At snapshot time:

1. `cargo check --manifest-path compiler-rust/Cargo.toml -q` passes.
2. `scripts/test_parser_ast_parity.sh` passes with full parity.
3. Single-thread in-process benchmark (`benchmark_cold_repeat`) passes.

