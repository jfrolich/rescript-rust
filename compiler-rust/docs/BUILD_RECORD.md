# Incremental build record: size and write cost

## Scope and reproducibility

Baseline: `44c6479bb`, stored schema 22, release build (fat LTO), eight workers,
Linux x86-64. Measurements here are not measurements on the target macOS machine.
Each package owns `lib/rescript/rescript.sqlite`. No write is moved earlier.

**Application blocker:** the unmodified baseline cannot build the supplied
3,735-module application. Two existing attributes produce warning 101 configured
as an error; parsing stops before compilation or record creation. The diagnostic
comes from `binary_ast::ppx::collect_unused_attribute_warnings_structure` /
`warn_unused_attribute` in `compiler-rust/src/binary_ast/ppx.rs`, collected by
`driver.rs`. Neither the corpus nor its warning policy was changed. Consequently
application column sizes, package timings, compression results and successful
clean-build comparisons are unavailable, not zero. The historical 54 MB and
72 ms tail are context supplied with the task, not measurements made here.

The `tests/tests` build succeeds: `Compiled 724 modules`, `Finished compilation`.
The inventory includes its dependency package; database IDs below are sorted by
file size, not package name. Sources and warnings are never reproduced here.

Method: open each database read-only after a successful clean build. Count table
rows and non-NULL cells; query `sum(length(column))`, `dbstat` grouped by object,
`PRAGMA page_size` and `PRAGMA freelist_count`. Text lengths are SQLite character
counts (these stored keys/encodings are ASCII); BLOB lengths are bytes. Integer
lengths are their decimal text lengths, **not** their physical integer encoding.
Only `dbstat.pgsize` is an allocated-byte measurement; payload-column lengths
must not be added to page totals. Indexes and unused page space are included.
Example queries:

```sql
SELECT count(*), count(data), sum(length(data)) FROM interfaces;
SELECT name, count(*), sum(pgsize), sum(payload), sum(unused)
FROM dbstat GROUP BY name;
PRAGMA page_size;
PRAGMA freelist_count;
```

## Readers and derivability (schema 22)

All SQL readers below are in `rewatch/src/build/state_db.rs`. The next one-shot
incremental build reads these; watch startup also goes through incremental
planning. Subsequent watch iterations keep their registry and graph in memory.
Editor tooling uses the running watcher's typechecking/registry
(`rewatch/src/build/tooling.rs`), not a separate SQLite reader. Thus absence of
an editor SQL reader does **not** make stored signatures disposable.

| Table.column | Reader and consumer | Can it be derived without losing behavior? |
| --- | --- | --- |
| meta.key, value | `read_meta_from`; `compiler_info` validates compiler/config identity; `PackageRecord::new`, `everything_up_to_date`, `outputs_as_recorded`, `imports_consistent` | Build start/success and previous compiler identity cannot come from current sources. Output paths can be recomputed, but the previous output set detects deletion/config changes. Runtime key validates the cache. |
| sources.path, module | `read_sources`; `PackageRecord::new`, `recorded_as_is` | Current discovery gives current paths, not deleted/renamed paths from the previous build. Both sides are needed. |
| modules.module | `read_modules`, keyed module lookup | Could use a shared integer module dictionary, at lookup/conversion cost; not simply delete. |
| modules.js_confirmed_at | `read_modules`; `PackageRecord::js_confirmed_at`, `compute_module_times`, `everything_up_to_date` | Not the JS mtime: unchanged generated output may be older than its last verified source. |
| modules.implementation_warnings, interface_warnings | `read_modules`; `restore_warnings` | Re-typechecking could regenerate warnings, but would compile unchanged modules and violate the no-op requirement. |
| modules.interface_digest | `read_modules`; `recorded_digests`, `next_round` | Derivable from item digests, but eagerly reading every item's cold payload would replace a cheap header read. Not the stored-interface hash (which also includes locations). |
| modules.imports | `read_modules`, lazy `Imports::list`; `plan`, `next_round`, `decode_recorded_imports` | Related to `reads`, but stores whole-interface digests including verified imports. The item-read aggregate digest is a different quantity. |
| parse_warnings.source, text | `read_parse_warnings`; `restore_parse_warnings`, `restore_unparsed_parse_warnings` | Re-parsing regenerates them at the cost of parsing untouched sources. |
| deps.source, mtime | `read_deps`; `seed_recorded_deps`, `collect_source_mtimes` | Current mtimes cannot tell whether cached references were parsed from those contents. Source keys also distinguish implementation/interface. |
| deps.deps | `read_deps`; `seed_recorded_deps` | Derivable by parsing, but even a one-module edit needs the dependency graph for all modules. |
| deps.gentype_annotations, gentype_declarations | `read_deps`; `seed_recorded_deps`, `mark_missing_gentype_declarations` | Derivable by parsing/typechecking. Preserve declaration availability across restarts or imported genType declarations can be missing. |
| reads.module, data | `read_reads` / `decode_reads`; `affected_by_changed_imports` | Needed only for candidate dependents of changed interfaces. Cannot recover historical item reads from the provider's current interface. |
| items.module, data | `read_items` / `decode_items`; `UnitDigests::get`, `plan` | Can hash decoded stored signatures, but would require decoding cold interfaces instead of reading compact item digests. |
| interfaces.module, hash | `read_stored_interface_hashes`; `current_record` | Hash can be recomputed from core plus extras, at the cost of reading/hashing every old blob before deciding whether to rewrite it. |
| interfaces.data | `InterfaceCores::read`; `load_stored`, `PendingCore::Fetch`, `stored_module::decode_core` | Recompile dependencies from source, defeating incremental compilation. Contains portable signature and JS metadata. Lossless compression is possible. |
| interface_extras.module, data | `read_interface_extras`; `load_stored`, `stored_module::decode_extras` | Imported genType declarations must be registered before dependent compilation. Re-typechecking is not a free derivation. Lossless compression is possible. |
| runtime_interfaces.module, data | `read_runtime_interfaces`; `compile::load_runtime_interfaces` | Can compile runtime sources, but that is precisely what the cache avoids. Embedded-runtime use leaves this table empty in this inventory. |

No unread column was found. Keys duplicated between tables are structural
lookup keys, not evidence that their payloads are redundant. `reads`, `items`
and `interfaces` are rowid tables with separate primary-key indexes; other
tables are `WITHOUT ROWID`. Empty tables still consume a root page each.

## Inventory: tests/tests

Total: **5,259,264 bytes** across 2 databases. All pages are 16,384 bytes;
there are no free-list pages. Percentages below use this total as denominator.

### Database 1: 4,849,664 bytes (92.21%)

| Object | Rows | Pages | Allocated bytes | Total share | Payload bytes | Unused bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| deps | 750 | 4 | 65,536 | 1.25% | 39,180 | 24,050 |
| interface_extras | 0 | 1 | 16,384 | 0.31% | 0 | 16,376 |
| interfaces | 718 | 252 | 4,128,768 | 78.50% | 3,773,735 | 348,278 |
| items | 718 | 13 | 212,992 | 4.05% | 179,574 | 29,337 |
| meta | 10 | 2 | 32,768 | 0.62% | 19,444 | 13,276 |
| modules | 718 | 4 | 65,536 | 1.25% | 43,289 | 20,030 |
| parse_warnings | 1 | 1 | 16,384 | 0.31% | 500 | 15,872 |
| reads | 718 | 4 | 65,536 | 1.25% | 32,449 | 29,547 |
| runtime_interfaces | 0 | 1 | 16,384 | 0.31% | 0 | 16,376 |
| sources | 750 | 4 | 65,536 | 1.25% | 34,048 | 29,194 |
| sqlite_autoindex_interfaces_1 | — | 3 | 49,152 | 0.93% | 15,606 | 31,360 |
| sqlite_autoindex_items_1 | — | 3 | 49,152 | 0.93% | 15,606 | 31,360 |
| sqlite_autoindex_reads_1 | — | 3 | 49,152 | 0.93% | 15,606 | 31,360 |
| sqlite_schema | — | 1 | 16,384 | 0.31% | 1,469 | 14,750 |
| Free-list | — | 0 | 0 | 0% | — | — |

| Column | Rows | Non-NULL | sum(length) | Total share (logical) |
| --- | ---: | ---: | ---: | ---: |
| meta.key | 10 | 10 | 165 | 0.003% |
| meta.value | 10 | 10 | 19,244 | 0.366% |
| sources.path | 750 | 750 | 19,090 | 0.363% |
| sources.module | 750 | 750 | 12,708 | 0.242% |
| modules.module | 718 | 718 | 12,144 | 0.231% |
| modules.js_confirmed_at | 718 | 718 | 13,642 | 0.259% |
| modules.implementation_warnings | 718 | 0 | 0 | 0.000% |
| modules.interface_warnings | 718 | 0 | 0 | 0.000% |
| modules.interface_digest | 718 | 718 | 13,935 | 0.265% |
| modules.imports | 718 | 718 | 14,600 | 0.278% |
| parse_warnings.source | 1 | 1 | 24 | 0.000% |
| parse_warnings.text | 1 | 1 | 462 | 0.009% |
| deps.source | 750 | 750 | 16,458 | 0.313% |
| deps.mtime | 750 | 750 | 14,250 | 0.271% |
| deps.deps | 750 | 750 | 12,190 | 0.232% |
| deps.gentype_annotations | 750 | 750 | 750 | 0.014% |
| deps.gentype_declarations | 750 | 750 | 750 | 0.014% |
| reads.module | 718 | 718 | 12,144 | 0.231% |
| reads.data | 718 | 718 | 18,100 | 0.344% |
| items.module | 718 | 718 | 12,144 | 0.231% |
| items.data | 718 | 718 | 164,615 | 3.130% |
| interfaces.module | 718 | 718 | 12,144 | 0.231% |
| interfaces.hash | 718 | 718 | 13,914 | 0.265% |
| interfaces.data | 718 | 718 | 3,752,204 | 71.345% |
| interface_extras.module | 0 | 0 | 0 | 0.000% |
| interface_extras.data | 0 | 0 | 0 | 0.000% |
| runtime_interfaces.module | 0 | 0 | 0 | 0.000% |
| runtime_interfaces.data | 0 | 0 | 0 | 0.000% |

### Database 2: 409,600 bytes (7.79%)

| Object | Rows | Pages | Allocated bytes | Total share | Payload bytes | Unused bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| deps | 9 | 1 | 16,384 | 0.31% | 978 | 15,369 |
| interface_extras | 0 | 1 | 16,384 | 0.31% | 0 | 16,376 |
| interfaces | 6 | 12 | 196,608 | 3.74% | 163,726 | 32,755 |
| items | 6 | 1 | 16,384 | 0.31% | 6,257 | 10,089 |
| meta | 9 | 1 | 16,384 | 0.31% | 598 | 15,750 |
| modules | 6 | 1 | 16,384 | 0.31% | 316 | 16,042 |
| parse_warnings | 0 | 1 | 16,384 | 0.31% | 0 | 16,376 |
| reads | 6 | 1 | 16,384 | 0.31% | 275 | 16,077 |
| runtime_interfaces | 0 | 1 | 16,384 | 0.31% | 0 | 16,376 |
| sources | 9 | 1 | 16,384 | 0.31% | 374 | 15,975 |
| sqlite_autoindex_interfaces_1 | — | 1 | 16,384 | 0.31% | 104 | 16,254 |
| sqlite_autoindex_items_1 | — | 1 | 16,384 | 0.31% | 104 | 16,254 |
| sqlite_autoindex_reads_1 | — | 1 | 16,384 | 0.31% | 104 | 16,254 |
| sqlite_schema | — | 1 | 16,384 | 0.31% | 1,469 | 14,750 |
| Free-list | — | 0 | 0 | 0% | — | — |

| Column | Rows | Non-NULL | sum(length) | Total share (logical) |
| --- | ---: | ---: | ---: | ---: |
| meta.key | 9 | 9 | 155 | 0.003% |
| meta.value | 9 | 9 | 412 | 0.008% |
| sources.path | 9 | 9 | 211 | 0.004% |
| sources.module | 9 | 9 | 136 | 0.003% |
| modules.module | 6 | 6 | 81 | 0.002% |
| modules.js_confirmed_at | 6 | 6 | 114 | 0.002% |
| modules.implementation_warnings | 6 | 0 | 0 | 0.000% |
| modules.interface_warnings | 6 | 0 | 0 | 0.000% |
| modules.interface_digest | 6 | 6 | 117 | 0.002% |
| modules.imports | 6 | 6 | 97 | 0.002% |
| parse_warnings.source | 0 | 0 | 0 | 0.000% |
| parse_warnings.text | 0 | 0 | 0 | 0.000% |
| deps.source | 9 | 9 | 181 | 0.003% |
| deps.mtime | 9 | 9 | 171 | 0.003% |
| deps.deps | 9 | 9 | 669 | 0.013% |
| deps.gentype_annotations | 9 | 9 | 9 | 0.000% |
| deps.gentype_declarations | 9 | 9 | 9 | 0.000% |
| reads.module | 6 | 6 | 81 | 0.002% |
| reads.data | 6 | 6 | 175 | 0.003% |
| items.module | 6 | 6 | 81 | 0.002% |
| items.data | 6 | 6 | 6,152 | 0.117% |
| interfaces.module | 6 | 6 | 81 | 0.002% |
| interfaces.hash | 6 | 6 | 119 | 0.002% |
| interfaces.data | 6 | 6 | 163,564 | 3.110% |
| interface_extras.module | 0 | 0 | 0 | 0.000% |
| interface_extras.data | 0 | 0 | 0 | 0.000% |
| runtime_interfaces.module | 0 | 0 | 0 | 0.000% |
| runtime_interfaces.data | 0 | 0 | 0 | 0.000% |

## Write-side split

`RESCRIPT_PHASE_TIMINGS=1` was measured with a temporary, uncommitted timing
probe around `open_path_for_write` and `write_record`: open includes connection
creation and version query; schema includes old-version replacement, schema
transaction and connection pragmas; inserts includes the data transaction's
preparation and execution; commit is its `commit()`. Encoding before opening is
excluded. This environment variable is not implemented by the baseline itself.
One instrumented clean run, microseconds (not additive wall time: packages write
in parallel):

| Database | Open | Schema/setup | Inserts | Commit |
| --- | ---: | ---: | ---: | ---: |
| 1 | 1,410 | 207,141 | 59,271 | 35,724 |
| 2 | 6,871 | 215,158 | 10,346 | 3,104 |

These are virtualized Linux filesystem measurements and must not be substituted
for the target machine's timings. In particular, schema creation commits before
`synchronous=OFF` is applied in `open_path_for_write`, unlike record writes.

A minimal independent reproduction of the application blocker is a package
with `sources: "src"`, `warnings: {"error": "+101"}`, and this source:

```rescript
@string
type t = First | Second
```

The baseline reports `Warning number 101 (configured as error)`,
`Unused attribute: @string`, then
`Build failed: could not parse the source files above.`
