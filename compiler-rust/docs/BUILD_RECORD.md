# Incremental build record: size and write cost

## Scope and reproducibility

Baseline: `44c6479bb`, stored schema 22, release build (fat LTO), eight workers,
Linux x86-64. Measurements here are not measurements on the target macOS machine.
Each package owns `lib/rescript/rescript.sqlite`. No write is moved earlier.

The 3,735-module application builds successfully when invoked **from its own
working directory**, with no project path argument, using the benchmark script's
source-only runtime and Belt preparation. The initial inventory commit called
an invocation-dependent warning failure a baseline blocker; that diagnosis was
incorrect. No corpus sources or warning policy were changed. The successful
build reports `Parsed 3735 source files`, `Compiled 3735 modules` and
`Finished compilation`. The application build writes 12 databases totaling 49,758,208 bytes. Preparing
the runtime with the benchmark script adds a 2,949,120-byte database which the
application does not rewrite: **13 databases, 52,707,328 bytes** in total. Both
the write set and the separately prepared runtime are inventoried below.
The `tests/tests` build succeeds: `Compiled 724 modules`, `Finished compilation`.
The inventory includes its dependency package; database IDs below are sorted by
file size, not package name. Sources and warnings are never reproduced here.

Method: open each database read-only after a successful clean build. Count table
rows and non-NULL cells; query `sum(length(column))`, `dbstat` grouped by object,
`PRAGMA page_size` and `PRAGMA freelist_count`. Text lengths use `length(CAST(column AS BLOB))` to count UTF-8 bytes rather
than Unicode characters; BLOB lengths are bytes. Integer
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

| Column | Rows | Non-NULL | Logical length B | Total share (logical) |
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
| parse_warnings.text | 1 | 1 | 472 | 0.009% |
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

| Column | Rows | Non-NULL | Logical length B | Total share (logical) |
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


## Inventory: a 3,735-module application

The 12 databases rewritten by the application total **49,758,208 bytes**.
All use 16,384-byte pages and have zero free-list pages. Percentages in these
twelve tables use this write-set total; the separately prepared runtime is
listed as database 13 below. The complete record occupies **52,707,328 bytes**.

### Application database 1: 33,914,880 bytes (68.16%)

| Object | Rows | Pages | Allocated bytes | Total share | Payload bytes | Unused bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| deps | 3564 | 54 | 884,736 | 1.778% | 727,125 | 144,434 |
| interface_extras | 2122 | 123 | 2,015,232 | 4.050% | 1,419,724 | 586,137 |
| interfaces | 3510 | 1142 | 18,710,528 | 37.603% | 16,068,911 | 2,605,424 |
| items | 3510 | 76 | 1,245,184 | 2.502% | 1,142,494 | 81,782 |
| meta | 9 | 19 | 311,296 | 0.626% | 285,039 | 26,144 |
| modules | 3510 | 280 | 4,587,520 | 9.220% | 2,869,227 | 1,701,982 |
| parse_warnings | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| reads | 3510 | 332 | 5,439,488 | 10.932% | 4,714,453 | 699,167 |
| runtime_interfaces | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sources | 3564 | 17 | 278,528 | 0.560% | 216,026 | 51,609 |
| sqlite_autoindex_interfaces_1 | — | 8 | 131,072 | 0.263% | 90,212 | 30,238 |
| sqlite_autoindex_items_1 | — | 8 | 131,072 | 0.263% | 90,212 | 30,238 |
| sqlite_autoindex_reads_1 | — | 8 | 131,072 | 0.263% | 90,212 | 30,238 |
| sqlite_schema | — | 1 | 16,384 | 0.033% | 1,469 | 14,750 |
| Free-list | — | 0 | 0 | 0% | — | — |

| Column | Rows | Non-NULL | Logical length B | Total share (logical) |
| --- | ---: | ---: | ---: | ---: |
| meta.key | 9 | 9 | 155 | 0.0003% |
| meta.value | 9 | 9 | 284,853 | 0.5725% |
| sources.path | 3564 | 3564 | 131,728 | 0.2647% |
| sources.module | 3564 | 3564 | 73,563 | 0.1478% |
| modules.module | 3510 | 3510 | 72,790 | 0.1463% |
| modules.js_confirmed_at | 3510 | 3510 | 66,690 | 0.1340% |
| modules.implementation_warnings | 3510 | 17 | 16,817 | 0.0338% |
| modules.interface_warnings | 3510 | 0 | 0 | 0.0000% |
| modules.interface_digest | 3510 | 3510 | 68,094 | 0.1368% |
| modules.imports | 3510 | 3510 | 2,695,850 | 5.4179% |
| parse_warnings.source | 0 | 0 | 0 | 0.0000% |
| parse_warnings.text | 0 | 0 | 0 | 0.0000% |
| deps.source | 3564 | 3564 | 91,383 | 0.1837% |
| deps.mtime | 3564 | 3564 | 67,716 | 0.1361% |
| deps.deps | 3564 | 3564 | 583,650 | 1.1730% |
| deps.gentype_annotations | 3564 | 3564 | 3,564 | 0.0072% |
| deps.gentype_declarations | 3564 | 3564 | 3,564 | 0.0072% |
| reads.module | 3510 | 3510 | 72,790 | 0.1463% |
| reads.data | 3510 | 3510 | 4,627,757 | 9.3005% |
| items.module | 3510 | 3510 | 72,790 | 0.1463% |
| items.data | 3510 | 3510 | 1,055,786 | 2.1218% |
| interfaces.module | 3510 | 3510 | 72,790 | 0.1463% |
| interfaces.hash | 3510 | 3510 | 68,108 | 0.1369% |
| interfaces.data | 3510 | 3510 | 15,950,078 | 32.0552% |
| interface_extras.module | 2122 | 2122 | 40,421 | 0.0812% |
| interface_extras.data | 2122 | 2122 | 1,370,797 | 2.7549% |
| runtime_interfaces.module | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.data | 0 | 0 | 0 | 0.0000% |

### Application database 2: 6,914,048 bytes (13.90%)

| Object | Rows | Pages | Allocated bytes | Total share | Payload bytes | Unused bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| deps | 122 | 3 | 49,152 | 0.099% | 18,433 | 30,278 |
| interface_extras | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| interfaces | 117 | 362 | 5,931,008 | 11.920% | 5,716,013 | 212,224 |
| items | 117 | 41 | 671,744 | 1.350% | 555,201 | 115,461 |
| meta | 9 | 2 | 32,768 | 0.066% | 5,774 | 26,950 |
| modules | 117 | 3 | 49,152 | 0.099% | 21,318 | 27,403 |
| parse_warnings | 2 | 1 | 16,384 | 0.033% | 1,638 | 14,730 |
| reads | 117 | 3 | 49,152 | 0.099% | 23,621 | 24,977 |
| runtime_interfaces | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sources | 122 | 1 | 16,384 | 0.033% | 8,520 | 7,490 |
| sqlite_autoindex_interfaces_1 | — | 1 | 16,384 | 0.033% | 3,319 | 12,706 |
| sqlite_autoindex_items_1 | — | 1 | 16,384 | 0.033% | 3,319 | 12,706 |
| sqlite_autoindex_reads_1 | — | 1 | 16,384 | 0.033% | 3,319 | 12,706 |
| sqlite_schema | — | 1 | 16,384 | 0.033% | 1,469 | 14,750 |
| Free-list | — | 0 | 0 | 0% | — | — |

| Column | Rows | Non-NULL | Logical length B | Total share (logical) |
| --- | ---: | ---: | ---: | ---: |
| meta.key | 9 | 9 | 155 | 0.0003% |
| meta.value | 9 | 9 | 5,589 | 0.0112% |
| sources.path | 122 | 122 | 5,198 | 0.0104% |
| sources.module | 122 | 122 | 2,953 | 0.0059% |
| modules.module | 117 | 117 | 2,852 | 0.0057% |
| modules.js_confirmed_at | 117 | 117 | 2,223 | 0.0045% |
| modules.implementation_warnings | 117 | 0 | 0 | 0.0000% |
| modules.interface_warnings | 117 | 0 | 0 | 0.0000% |
| modules.interface_digest | 117 | 117 | 2,269 | 0.0046% |
| modules.imports | 117 | 117 | 15,706 | 0.0316% |
| parse_warnings.source | 2 | 2 | 42 | 0.0001% |
| parse_warnings.text | 2 | 2 | 1,588 | 0.0032% |
| deps.source | 122 | 122 | 3,563 | 0.0072% |
| deps.mtime | 122 | 122 | 2,318 | 0.0047% |
| deps.deps | 122 | 122 | 13,112 | 0.0264% |
| deps.gentype_annotations | 122 | 122 | 122 | 0.0002% |
| deps.gentype_declarations | 122 | 122 | 122 | 0.0002% |
| reads.module | 117 | 117 | 2,852 | 0.0057% |
| reads.data | 117 | 117 | 20,347 | 0.0409% |
| items.module | 117 | 117 | 2,852 | 0.0057% |
| items.data | 117 | 117 | 551,852 | 1.1091% |
| interfaces.module | 117 | 117 | 2,852 | 0.0057% |
| interfaces.hash | 117 | 117 | 2,262 | 0.0045% |
| interfaces.data | 117 | 117 | 5,711,594 | 11.4787% |
| interface_extras.module | 0 | 0 | 0 | 0.0000% |
| interface_extras.data | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.module | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.data | 0 | 0 | 0 | 0.0000% |

### Application database 3: 2,867,200 bytes (5.76%)

| Object | Rows | Pages | Allocated bytes | Total share | Payload bytes | Unused bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| deps | 39 | 1 | 16,384 | 0.033% | 2,725 | 13,529 |
| interface_extras | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| interfaces | 39 | 160 | 2,621,440 | 5.268% | 2,534,927 | 85,367 |
| items | 39 | 3 | 49,152 | 0.099% | 26,746 | 22,179 |
| meta | 9 | 1 | 16,384 | 0.033% | 1,118 | 15,230 |
| modules | 39 | 1 | 16,384 | 0.033% | 4,300 | 11,949 |
| parse_warnings | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| reads | 39 | 1 | 16,384 | 0.033% | 5,380 | 10,824 |
| runtime_interfaces | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sources | 39 | 1 | 16,384 | 0.033% | 1,251 | 15,008 |
| sqlite_autoindex_interfaces_1 | — | 1 | 16,384 | 0.033% | 698 | 15,561 |
| sqlite_autoindex_items_1 | — | 1 | 16,384 | 0.033% | 698 | 15,561 |
| sqlite_autoindex_reads_1 | — | 1 | 16,384 | 0.033% | 698 | 15,561 |
| sqlite_schema | — | 1 | 16,384 | 0.033% | 1,469 | 14,750 |
| Free-list | — | 0 | 0 | 0% | — | — |

| Column | Rows | Non-NULL | Logical length B | Total share (logical) |
| --- | ---: | ---: | ---: | ---: |
| meta.key | 9 | 9 | 155 | 0.0003% |
| meta.value | 9 | 9 | 933 | 0.0019% |
| sources.path | 39 | 39 | 591 | 0.0012% |
| sources.module | 39 | 39 | 543 | 0.0011% |
| modules.module | 39 | 39 | 543 | 0.0011% |
| modules.js_confirmed_at | 39 | 39 | 741 | 0.0015% |
| modules.implementation_warnings | 39 | 0 | 0 | 0.0000% |
| modules.interface_warnings | 39 | 0 | 0 | 0.0000% |
| modules.interface_digest | 39 | 39 | 761 | 0.0015% |
| modules.imports | 39 | 39 | 2,843 | 0.0057% |
| parse_warnings.source | 0 | 0 | 0 | 0.0000% |
| parse_warnings.text | 0 | 0 | 0 | 0.0000% |
| deps.source | 39 | 39 | 738 | 0.0015% |
| deps.mtime | 39 | 39 | 741 | 0.0015% |
| deps.deps | 39 | 39 | 1,430 | 0.0029% |
| deps.gentype_annotations | 39 | 39 | 39 | 0.0001% |
| deps.gentype_declarations | 39 | 39 | 39 | 0.0001% |
| reads.module | 39 | 39 | 543 | 0.0011% |
| reads.data | 39 | 39 | 4,696 | 0.0094% |
| items.module | 39 | 39 | 543 | 0.0011% |
| items.data | 39 | 39 | 26,047 | 0.0523% |
| interfaces.module | 39 | 39 | 543 | 0.0011% |
| interfaces.hash | 39 | 39 | 756 | 0.0015% |
| interfaces.data | 39 | 39 | 2,533,854 | 5.0923% |
| interface_extras.module | 0 | 0 | 0 | 0.0000% |
| interface_extras.data | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.module | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.data | 0 | 0 | 0 | 0.0000% |

### Application database 4: 1,769,472 bytes (3.56%)

| Object | Rows | Pages | Allocated bytes | Total share | Payload bytes | Unused bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| deps | 8 | 1 | 16,384 | 0.033% | 3,602 | 12,748 |
| interface_extras | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| interfaces | 5 | 92 | 1,507,328 | 3.029% | 1,458,947 | 47,912 |
| items | 5 | 4 | 65,536 | 0.132% | 38,362 | 27,100 |
| meta | 9 | 1 | 16,384 | 0.033% | 524 | 15,825 |
| modules | 5 | 1 | 16,384 | 0.033% | 611 | 15,748 |
| parse_warnings | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| reads | 5 | 1 | 16,384 | 0.033% | 819 | 15,534 |
| runtime_interfaces | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sources | 8 | 1 | 16,384 | 0.033% | 291 | 16,061 |
| sqlite_autoindex_interfaces_1 | — | 1 | 16,384 | 0.033% | 78 | 16,283 |
| sqlite_autoindex_items_1 | — | 1 | 16,384 | 0.033% | 78 | 16,283 |
| sqlite_autoindex_reads_1 | — | 1 | 16,384 | 0.033% | 78 | 16,283 |
| sqlite_schema | — | 1 | 16,384 | 0.033% | 1,469 | 14,750 |
| Free-list | — | 0 | 0 | 0% | — | — |

| Column | Rows | Non-NULL | Logical length B | Total share (logical) |
| --- | ---: | ---: | ---: | ---: |
| meta.key | 9 | 9 | 155 | 0.0003% |
| meta.value | 9 | 9 | 339 | 0.0007% |
| sources.path | 8 | 8 | 167 | 0.0003% |
| sources.module | 8 | 8 | 100 | 0.0002% |
| modules.module | 5 | 5 | 59 | 0.0001% |
| modules.js_confirmed_at | 5 | 5 | 95 | 0.0002% |
| modules.implementation_warnings | 5 | 0 | 0 | 0.0000% |
| modules.interface_warnings | 5 | 0 | 0 | 0.0000% |
| modules.interface_digest | 5 | 5 | 96 | 0.0002% |
| modules.imports | 5 | 5 | 434 | 0.0009% |
| parse_warnings.source | 0 | 0 | 0 | 0.0000% |
| parse_warnings.text | 0 | 0 | 0 | 0.0000% |
| deps.source | 8 | 8 | 140 | 0.0003% |
| deps.mtime | 8 | 8 | 152 | 0.0003% |
| deps.deps | 8 | 8 | 3,348 | 0.0067% |
| deps.gentype_annotations | 8 | 8 | 8 | 0.0000% |
| deps.gentype_declarations | 8 | 8 | 8 | 0.0000% |
| reads.module | 5 | 5 | 59 | 0.0001% |
| reads.data | 5 | 5 | 742 | 0.0015% |
| items.module | 5 | 5 | 59 | 0.0001% |
| items.data | 5 | 5 | 38,281 | 0.0769% |
| interfaces.module | 5 | 5 | 59 | 0.0001% |
| interfaces.hash | 5 | 5 | 94 | 0.0002% |
| interfaces.data | 5 | 5 | 1,458,819 | 2.9318% |
| interface_extras.module | 0 | 0 | 0 | 0.0000% |
| interface_extras.data | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.module | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.data | 0 | 0 | 0 | 0.0000% |

### Application database 5: 1,703,936 bytes (3.42%)

| Object | Rows | Pages | Allocated bytes | Total share | Payload bytes | Unused bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| deps | 2 | 1 | 16,384 | 0.033% | 226 | 16,144 |
| interface_extras | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| interfaces | 2 | 89 | 1,458,176 | 2.931% | 1,437,222 | 20,555 |
| items | 2 | 3 | 49,152 | 0.099% | 39,256 | 9,860 |
| meta | 9 | 1 | 16,384 | 0.033% | 439 | 15,910 |
| modules | 2 | 1 | 16,384 | 0.033% | 404 | 15,964 |
| parse_warnings | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| reads | 2 | 1 | 16,384 | 0.033% | 1,701 | 14,665 |
| runtime_interfaces | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sources | 2 | 1 | 16,384 | 0.033% | 38 | 16,332 |
| sqlite_autoindex_interfaces_1 | — | 1 | 16,384 | 0.033% | 15 | 16,355 |
| sqlite_autoindex_items_1 | — | 1 | 16,384 | 0.033% | 15 | 16,355 |
| sqlite_autoindex_reads_1 | — | 1 | 16,384 | 0.033% | 15 | 16,355 |
| sqlite_schema | — | 1 | 16,384 | 0.033% | 1,469 | 14,750 |
| Free-list | — | 0 | 0 | 0% | — | — |

| Column | Rows | Non-NULL | Logical length B | Total share (logical) |
| --- | ---: | ---: | ---: | ---: |
| meta.key | 9 | 9 | 155 | 0.0003% |
| meta.value | 9 | 9 | 255 | 0.0005% |
| sources.path | 2 | 2 | 24 | 0.0000% |
| sources.module | 2 | 2 | 8 | 0.0000% |
| modules.module | 2 | 2 | 8 | 0.0000% |
| modules.js_confirmed_at | 2 | 2 | 38 | 0.0001% |
| modules.implementation_warnings | 2 | 0 | 0 | 0.0000% |
| modules.interface_warnings | 2 | 0 | 0 | 0.0000% |
| modules.interface_digest | 2 | 2 | 39 | 0.0001% |
| modules.imports | 2 | 2 | 348 | 0.0007% |
| parse_warnings.source | 0 | 0 | 0 | 0.0000% |
| parse_warnings.text | 0 | 0 | 0 | 0.0000% |
| deps.source | 2 | 2 | 18 | 0.0000% |
| deps.mtime | 2 | 2 | 38 | 0.0001% |
| deps.deps | 2 | 2 | 178 | 0.0004% |
| deps.gentype_annotations | 2 | 2 | 2 | 0.0000% |
| deps.gentype_declarations | 2 | 2 | 2 | 0.0000% |
| reads.module | 2 | 2 | 8 | 0.0000% |
| reads.data | 2 | 2 | 1,685 | 0.0034% |
| items.module | 2 | 2 | 8 | 0.0000% |
| items.data | 2 | 2 | 39,238 | 0.0789% |
| interfaces.module | 2 | 2 | 8 | 0.0000% |
| interfaces.hash | 2 | 2 | 38 | 0.0001% |
| interfaces.data | 2 | 2 | 1,437,186 | 2.8883% |
| interface_extras.module | 0 | 0 | 0 | 0.0000% |
| interface_extras.data | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.module | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.data | 0 | 0 | 0 | 0.0000% |

### Application database 6: 983,040 bytes (1.98%)

| Object | Rows | Pages | Allocated bytes | Total share | Payload bytes | Unused bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| deps | 81 | 1 | 16,384 | 0.033% | 5,247 | 10,882 |
| interface_extras | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| interfaces | 43 | 44 | 720,896 | 1.449% | 627,468 | 92,734 |
| items | 43 | 4 | 65,536 | 0.132% | 37,356 | 27,915 |
| meta | 9 | 1 | 16,384 | 0.033% | 1,524 | 14,824 |
| modules | 43 | 1 | 16,384 | 0.033% | 6,264 | 9,958 |
| parse_warnings | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| reads | 43 | 1 | 16,384 | 0.033% | 6,143 | 10,034 |
| runtime_interfaces | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sources | 81 | 1 | 16,384 | 0.033% | 3,321 | 12,812 |
| sqlite_autoindex_interfaces_1 | — | 1 | 16,384 | 0.033% | 812 | 15,435 |
| sqlite_autoindex_items_1 | — | 1 | 16,384 | 0.033% | 812 | 15,435 |
| sqlite_autoindex_reads_1 | — | 1 | 16,384 | 0.033% | 812 | 15,435 |
| sqlite_schema | — | 1 | 16,384 | 0.033% | 1,469 | 14,750 |
| Free-list | — | 0 | 0 | 0% | — | — |

| Column | Rows | Non-NULL | Logical length B | Total share (logical) |
| --- | ---: | ---: | ---: | ---: |
| meta.key | 9 | 9 | 155 | 0.0003% |
| meta.value | 9 | 9 | 1,339 | 0.0027% |
| sources.path | 81 | 81 | 1,882 | 0.0038% |
| sources.module | 81 | 81 | 1,196 | 0.0024% |
| modules.module | 43 | 43 | 641 | 0.0013% |
| modules.js_confirmed_at | 43 | 43 | 817 | 0.0016% |
| modules.implementation_warnings | 43 | 0 | 0 | 0.0000% |
| modules.interface_warnings | 43 | 0 | 0 | 0.0000% |
| modules.interface_digest | 43 | 43 | 839 | 0.0017% |
| modules.imports | 43 | 43 | 4,603 | 0.0093% |
| parse_warnings.source | 0 | 0 | 0 | 0.0000% |
| parse_warnings.text | 0 | 0 | 0 | 0.0000% |
| deps.source | 81 | 81 | 1,601 | 0.0032% |
| deps.mtime | 81 | 81 | 1,539 | 0.0031% |
| deps.deps | 81 | 81 | 2,499 | 0.0050% |
| deps.gentype_annotations | 81 | 81 | 81 | 0.0002% |
| deps.gentype_declarations | 81 | 81 | 81 | 0.0002% |
| reads.module | 43 | 43 | 641 | 0.0013% |
| reads.data | 43 | 43 | 5,342 | 0.0107% |
| items.module | 43 | 43 | 641 | 0.0013% |
| items.data | 43 | 43 | 36,543 | 0.0734% |
| interfaces.module | 43 | 43 | 641 | 0.0013% |
| interfaces.hash | 43 | 43 | 831 | 0.0017% |
| interfaces.data | 43 | 43 | 626,245 | 1.2586% |
| interface_extras.module | 0 | 0 | 0 | 0.0000% |
| interface_extras.data | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.module | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.data | 0 | 0 | 0 | 0.0000% |

### Application database 7: 425,984 bytes (0.86%)

| Object | Rows | Pages | Allocated bytes | Total share | Payload bytes | Unused bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| deps | 13 | 1 | 16,384 | 0.033% | 1,166 | 15,169 |
| interface_extras | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| interfaces | 9 | 13 | 212,992 | 0.428% | 181,515 | 31,320 |
| items | 9 | 1 | 16,384 | 0.033% | 7,403 | 8,928 |
| meta | 9 | 1 | 16,384 | 0.033% | 632 | 15,716 |
| modules | 9 | 1 | 16,384 | 0.033% | 525 | 15,824 |
| parse_warnings | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| reads | 9 | 1 | 16,384 | 0.033% | 539 | 15,800 |
| runtime_interfaces | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sources | 13 | 1 | 16,384 | 0.033% | 531 | 15,806 |
| sqlite_autoindex_interfaces_1 | — | 1 | 16,384 | 0.033% | 158 | 16,191 |
| sqlite_autoindex_items_1 | — | 1 | 16,384 | 0.033% | 158 | 16,191 |
| sqlite_autoindex_reads_1 | — | 1 | 16,384 | 0.033% | 158 | 16,191 |
| sqlite_schema | — | 1 | 16,384 | 0.033% | 1,469 | 14,750 |
| Free-list | — | 0 | 0 | 0% | — | — |

| Column | Rows | Non-NULL | Logical length B | Total share (logical) |
| --- | ---: | ---: | ---: | ---: |
| meta.key | 9 | 9 | 155 | 0.0003% |
| meta.value | 9 | 9 | 447 | 0.0009% |
| sources.path | 13 | 13 | 300 | 0.0006% |
| sources.module | 13 | 13 | 192 | 0.0004% |
| modules.module | 9 | 9 | 123 | 0.0002% |
| modules.js_confirmed_at | 9 | 9 | 171 | 0.0003% |
| modules.implementation_warnings | 9 | 0 | 0 | 0.0000% |
| modules.interface_warnings | 9 | 0 | 0 | 0.0000% |
| modules.interface_digest | 9 | 9 | 173 | 0.0003% |
| modules.imports | 9 | 9 | 195 | 0.0004% |
| parse_warnings.source | 0 | 0 | 0 | 0.0000% |
| parse_warnings.text | 0 | 0 | 0 | 0.0000% |
| deps.source | 13 | 13 | 257 | 0.0005% |
| deps.mtime | 13 | 13 | 247 | 0.0005% |
| deps.deps | 13 | 13 | 725 | 0.0015% |
| deps.gentype_annotations | 13 | 13 | 13 | 0.0000% |
| deps.gentype_declarations | 13 | 13 | 13 | 0.0000% |
| reads.module | 9 | 9 | 123 | 0.0002% |
| reads.data | 9 | 9 | 387 | 0.0008% |
| items.module | 9 | 9 | 123 | 0.0002% |
| items.data | 9 | 9 | 7,244 | 0.0146% |
| interfaces.module | 9 | 9 | 123 | 0.0002% |
| interfaces.hash | 9 | 9 | 176 | 0.0004% |
| interfaces.data | 9 | 9 | 181,272 | 0.3643% |
| interface_extras.module | 0 | 0 | 0 | 0.0000% |
| interface_extras.data | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.module | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.data | 0 | 0 | 0 | 0.0000% |

### Application database 8: 262,144 bytes (0.53%)

| Object | Rows | Pages | Allocated bytes | Total share | Payload bytes | Unused bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| deps | 2 | 1 | 16,384 | 0.033% | 147 | 16,223 |
| interface_extras | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| interfaces | 2 | 3 | 49,152 | 0.099% | 17,731 | 31,376 |
| items | 2 | 1 | 16,384 | 0.033% | 1,395 | 14,971 |
| meta | 9 | 1 | 16,384 | 0.033% | 466 | 15,883 |
| modules | 2 | 1 | 16,384 | 0.033% | 92 | 16,278 |
| parse_warnings | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| reads | 2 | 1 | 16,384 | 0.033% | 54 | 16,314 |
| runtime_interfaces | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sources | 2 | 1 | 16,384 | 0.033% | 74 | 16,296 |
| sqlite_autoindex_interfaces_1 | — | 1 | 16,384 | 0.033% | 24 | 16,346 |
| sqlite_autoindex_items_1 | — | 1 | 16,384 | 0.033% | 24 | 16,346 |
| sqlite_autoindex_reads_1 | — | 1 | 16,384 | 0.033% | 24 | 16,346 |
| sqlite_schema | — | 1 | 16,384 | 0.033% | 1,469 | 14,750 |
| Free-list | — | 0 | 0 | 0% | — | — |

| Column | Rows | Non-NULL | Logical length B | Total share (logical) |
| --- | ---: | ---: | ---: | ---: |
| meta.key | 9 | 9 | 155 | 0.0003% |
| meta.value | 9 | 9 | 282 | 0.0006% |
| sources.path | 2 | 2 | 51 | 0.0001% |
| sources.module | 2 | 2 | 17 | 0.0000% |
| modules.module | 2 | 2 | 17 | 0.0000% |
| modules.js_confirmed_at | 2 | 2 | 38 | 0.0001% |
| modules.implementation_warnings | 2 | 0 | 0 | 0.0000% |
| modules.interface_warnings | 2 | 0 | 0 | 0.0000% |
| modules.interface_digest | 2 | 2 | 38 | 0.0001% |
| modules.imports | 2 | 2 | 29 | 0.0001% |
| parse_warnings.source | 0 | 0 | 0 | 0.0000% |
| parse_warnings.text | 0 | 0 | 0 | 0.0000% |
| deps.source | 2 | 2 | 27 | 0.0001% |
| deps.mtime | 2 | 2 | 38 | 0.0001% |
| deps.deps | 2 | 2 | 91 | 0.0002% |
| deps.gentype_annotations | 2 | 2 | 2 | 0.0000% |
| deps.gentype_declarations | 2 | 2 | 2 | 0.0000% |
| reads.module | 2 | 2 | 17 | 0.0000% |
| reads.data | 2 | 2 | 31 | 0.0001% |
| items.module | 2 | 2 | 17 | 0.0000% |
| items.data | 2 | 2 | 1,370 | 0.0028% |
| interfaces.module | 2 | 2 | 17 | 0.0000% |
| interfaces.hash | 2 | 2 | 39 | 0.0001% |
| interfaces.data | 2 | 2 | 17,687 | 0.0355% |
| interface_extras.module | 0 | 0 | 0 | 0.0000% |
| interface_extras.data | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.module | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.data | 0 | 0 | 0 | 0.0000% |

### Application database 9: 229,376 bytes (0.46%)

| Object | Rows | Pages | Allocated bytes | Total share | Payload bytes | Unused bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| deps | 6 | 1 | 16,384 | 0.033% | 427 | 15,930 |
| interface_extras | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| interfaces | 6 | 1 | 16,384 | 0.033% | 11,716 | 4,630 |
| items | 6 | 1 | 16,384 | 0.033% | 1,604 | 14,744 |
| meta | 9 | 1 | 16,384 | 0.033% | 529 | 15,819 |
| modules | 6 | 1 | 16,384 | 0.033% | 1,121 | 15,235 |
| parse_warnings | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| reads | 6 | 1 | 16,384 | 0.033% | 1,589 | 14,761 |
| runtime_interfaces | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sources | 6 | 1 | 16,384 | 0.033% | 172 | 16,186 |
| sqlite_autoindex_interfaces_1 | — | 1 | 16,384 | 0.033% | 76 | 16,282 |
| sqlite_autoindex_items_1 | — | 1 | 16,384 | 0.033% | 76 | 16,282 |
| sqlite_autoindex_reads_1 | — | 1 | 16,384 | 0.033% | 76 | 16,282 |
| sqlite_schema | — | 1 | 16,384 | 0.033% | 1,469 | 14,750 |
| Free-list | — | 0 | 0 | 0% | — | — |

| Column | Rows | Non-NULL | Logical length B | Total share (logical) |
| --- | ---: | ---: | ---: | ---: |
| meta.key | 9 | 9 | 155 | 0.0003% |
| meta.value | 9 | 9 | 344 | 0.0007% |
| sources.path | 6 | 6 | 101 | 0.0002% |
| sources.module | 6 | 6 | 53 | 0.0001% |
| modules.module | 6 | 6 | 53 | 0.0001% |
| modules.js_confirmed_at | 6 | 6 | 114 | 0.0002% |
| modules.implementation_warnings | 6 | 0 | 0 | 0.0000% |
| modules.interface_warnings | 6 | 0 | 0 | 0.0000% |
| modules.interface_digest | 6 | 6 | 117 | 0.0002% |
| modules.imports | 6 | 6 | 928 | 0.0019% |
| parse_warnings.source | 0 | 0 | 0 | 0.0000% |
| parse_warnings.text | 0 | 0 | 0 | 0.0000% |
| deps.source | 6 | 6 | 83 | 0.0002% |
| deps.mtime | 6 | 6 | 114 | 0.0002% |
| deps.deps | 6 | 6 | 259 | 0.0005% |
| deps.gentype_annotations | 6 | 6 | 6 | 0.0000% |
| deps.gentype_declarations | 6 | 6 | 6 | 0.0000% |
| reads.module | 6 | 6 | 53 | 0.0001% |
| reads.data | 6 | 6 | 1,516 | 0.0030% |
| items.module | 6 | 6 | 53 | 0.0001% |
| items.data | 6 | 6 | 1,527 | 0.0031% |
| interfaces.module | 6 | 6 | 53 | 0.0001% |
| interfaces.hash | 6 | 6 | 114 | 0.0002% |
| interfaces.data | 6 | 6 | 11,585 | 0.0233% |
| interface_extras.module | 0 | 0 | 0 | 0.0000% |
| interface_extras.data | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.module | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.data | 0 | 0 | 0 | 0.0000% |

### Application database 10: 229,376 bytes (0.46%)

| Object | Rows | Pages | Allocated bytes | Total share | Payload bytes | Unused bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| deps | 2 | 1 | 16,384 | 0.033% | 86 | 16,284 |
| interface_extras | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| interfaces | 1 | 1 | 16,384 | 0.033% | 1,129 | 15,242 |
| items | 1 | 1 | 16,384 | 0.033% | 119 | 16,253 |
| meta | 9 | 1 | 16,384 | 0.033% | 433 | 15,916 |
| modules | 1 | 1 | 16,384 | 0.033% | 84 | 16,289 |
| parse_warnings | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| reads | 1 | 1 | 16,384 | 0.033% | 119 | 16,253 |
| runtime_interfaces | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sources | 2 | 1 | 16,384 | 0.033% | 75 | 16,295 |
| sqlite_autoindex_interfaces_1 | — | 1 | 16,384 | 0.033% | 16 | 16,357 |
| sqlite_autoindex_items_1 | — | 1 | 16,384 | 0.033% | 16 | 16,357 |
| sqlite_autoindex_reads_1 | — | 1 | 16,384 | 0.033% | 16 | 16,357 |
| sqlite_schema | — | 1 | 16,384 | 0.033% | 1,469 | 14,750 |
| Free-list | — | 0 | 0 | 0% | — | — |

| Column | Rows | Non-NULL | Logical length B | Total share (logical) |
| --- | ---: | ---: | ---: | ---: |
| meta.key | 9 | 9 | 155 | 0.0003% |
| meta.value | 9 | 9 | 249 | 0.0005% |
| sources.path | 2 | 2 | 43 | 0.0001% |
| sources.module | 2 | 2 | 26 | 0.0001% |
| modules.module | 1 | 1 | 13 | 0.0000% |
| modules.js_confirmed_at | 1 | 1 | 19 | 0.0000% |
| modules.implementation_warnings | 1 | 0 | 0 | 0.0000% |
| modules.interface_warnings | 1 | 0 | 0 | 0.0000% |
| modules.interface_digest | 1 | 1 | 20 | 0.0000% |
| modules.imports | 1 | 1 | 48 | 0.0001% |
| parse_warnings.source | 0 | 0 | 0 | 0.0000% |
| parse_warnings.text | 0 | 0 | 0 | 0.0000% |
| deps.source | 2 | 2 | 36 | 0.0001% |
| deps.mtime | 2 | 2 | 38 | 0.0001% |
| deps.deps | 2 | 2 | 22 | 0.0000% |
| deps.gentype_annotations | 2 | 2 | 2 | 0.0000% |
| deps.gentype_declarations | 2 | 2 | 2 | 0.0000% |
| reads.module | 1 | 1 | 13 | 0.0000% |
| reads.data | 1 | 1 | 102 | 0.0002% |
| items.module | 1 | 1 | 13 | 0.0000% |
| items.data | 1 | 1 | 102 | 0.0002% |
| interfaces.module | 1 | 1 | 13 | 0.0000% |
| interfaces.hash | 1 | 1 | 20 | 0.0000% |
| interfaces.data | 1 | 1 | 1,103 | 0.0022% |
| interface_extras.module | 0 | 0 | 0 | 0.0000% |
| interface_extras.data | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.module | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.data | 0 | 0 | 0 | 0.0000% |

### Application database 11: 229,376 bytes (0.46%)

| Object | Rows | Pages | Allocated bytes | Total share | Payload bytes | Unused bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| deps | 2 | 1 | 16,384 | 0.033% | 62 | 16,308 |
| interface_extras | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| interfaces | 1 | 1 | 16,384 | 0.033% | 1,589 | 14,782 |
| items | 1 | 1 | 16,384 | 0.033% | 136 | 16,235 |
| meta | 9 | 1 | 16,384 | 0.033% | 428 | 15,921 |
| modules | 1 | 1 | 16,384 | 0.033% | 31 | 16,342 |
| parse_warnings | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| reads | 1 | 1 | 16,384 | 0.033% | 11 | 16,361 |
| runtime_interfaces | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sources | 2 | 1 | 16,384 | 0.033% | 55 | 16,315 |
| sqlite_autoindex_interfaces_1 | — | 1 | 16,384 | 0.033% | 11 | 16,362 |
| sqlite_autoindex_items_1 | — | 1 | 16,384 | 0.033% | 11 | 16,362 |
| sqlite_autoindex_reads_1 | — | 1 | 16,384 | 0.033% | 11 | 16,362 |
| sqlite_schema | — | 1 | 16,384 | 0.033% | 1,469 | 14,750 |
| Free-list | — | 0 | 0 | 0% | — | — |

| Column | Rows | Non-NULL | Logical length B | Total share (logical) |
| --- | ---: | ---: | ---: | ---: |
| meta.key | 9 | 9 | 155 | 0.0003% |
| meta.value | 9 | 9 | 244 | 0.0005% |
| sources.path | 2 | 2 | 33 | 0.0001% |
| sources.module | 2 | 2 | 16 | 0.0000% |
| modules.module | 1 | 1 | 8 | 0.0000% |
| modules.js_confirmed_at | 1 | 1 | 19 | 0.0000% |
| modules.implementation_warnings | 1 | 0 | 0 | 0.0000% |
| modules.interface_warnings | 1 | 0 | 0 | 0.0000% |
| modules.interface_digest | 1 | 1 | 19 | 0.0000% |
| modules.imports | 1 | 1 | 0 | 0.0000% |
| parse_warnings.source | 0 | 0 | 0 | 0.0000% |
| parse_warnings.text | 0 | 0 | 0 | 0.0000% |
| deps.source | 2 | 2 | 26 | 0.0001% |
| deps.mtime | 2 | 2 | 38 | 0.0001% |
| deps.deps | 2 | 2 | 8 | 0.0000% |
| deps.gentype_annotations | 2 | 2 | 2 | 0.0000% |
| deps.gentype_declarations | 2 | 2 | 2 | 0.0000% |
| reads.module | 1 | 1 | 8 | 0.0000% |
| reads.data | 1 | 1 | 0 | 0.0000% |
| items.module | 1 | 1 | 8 | 0.0000% |
| items.data | 1 | 1 | 124 | 0.0002% |
| interfaces.module | 1 | 1 | 8 | 0.0000% |
| interfaces.hash | 1 | 1 | 20 | 0.0000% |
| interfaces.data | 1 | 1 | 1,568 | 0.0032% |
| interface_extras.module | 0 | 0 | 0 | 0.0000% |
| interface_extras.data | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.module | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.data | 0 | 0 | 0 | 0.0000% |

### Application database 12: 229,376 bytes (0.46%)

| Object | Rows | Pages | Allocated bytes | Total share | Payload bytes | Unused bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| deps | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| interface_extras | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| interfaces | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| items | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| meta | 10 | 1 | 16,384 | 0.033% | 439 | 15,907 |
| modules | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| parse_warnings | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| reads | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| runtime_interfaces | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sources | 0 | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sqlite_autoindex_interfaces_1 | — | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sqlite_autoindex_items_1 | — | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sqlite_autoindex_reads_1 | — | 1 | 16,384 | 0.033% | 0 | 16,376 |
| sqlite_schema | — | 1 | 16,384 | 0.033% | 1,469 | 14,750 |
| Free-list | — | 0 | 0 | 0% | — | — |

| Column | Rows | Non-NULL | Logical length B | Total share (logical) |
| --- | ---: | ---: | ---: | ---: |
| meta.key | 10 | 10 | 165 | 0.0003% |
| meta.value | 10 | 10 | 242 | 0.0005% |
| sources.path | 0 | 0 | 0 | 0.0000% |
| sources.module | 0 | 0 | 0 | 0.0000% |
| modules.module | 0 | 0 | 0 | 0.0000% |
| modules.js_confirmed_at | 0 | 0 | 0 | 0.0000% |
| modules.implementation_warnings | 0 | 0 | 0 | 0.0000% |
| modules.interface_warnings | 0 | 0 | 0 | 0.0000% |
| modules.interface_digest | 0 | 0 | 0 | 0.0000% |
| modules.imports | 0 | 0 | 0 | 0.0000% |
| parse_warnings.source | 0 | 0 | 0 | 0.0000% |
| parse_warnings.text | 0 | 0 | 0 | 0.0000% |
| deps.source | 0 | 0 | 0 | 0.0000% |
| deps.mtime | 0 | 0 | 0 | 0.0000% |
| deps.deps | 0 | 0 | 0 | 0.0000% |
| deps.gentype_annotations | 0 | 0 | 0 | 0.0000% |
| deps.gentype_declarations | 0 | 0 | 0 | 0.0000% |
| reads.module | 0 | 0 | 0 | 0.0000% |
| reads.data | 0 | 0 | 0 | 0.0000% |
| items.module | 0 | 0 | 0 | 0.0000% |
| items.data | 0 | 0 | 0 | 0.0000% |
| interfaces.module | 0 | 0 | 0 | 0.0000% |
| interfaces.hash | 0 | 0 | 0 | 0.0000% |
| interfaces.data | 0 | 0 | 0 | 0.0000% |
| interface_extras.module | 0 | 0 | 0 | 0.0000% |
| interface_extras.data | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.module | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.data | 0 | 0 | 0 | 0.0000% |

## Application write-side split

Same temporary timing probe and definitions as above. One successful clean run,
microseconds; IDs match the application inventory. These are concurrent package
transactions, so summing them does not give the wall-clock tail.

| Database | Open | Schema/setup | Inserts | Commit |
| --- | ---: | ---: | ---: | ---: |
| 1 | 244 | 2,863 | 30,622 | 25,040 |
| 2 | 349 | 8,401 | 10,847 | 6,166 |
| 3 | 264 | 3,697 | 3,454 | 1,586 |
| 4 | 495 | 10,281 | 3,354 | 1,661 |
| 5 | 169 | 3,426 | 2,218 | 1,427 |
| 6 | 163 | 5,849 | 1,760 | 468 |
| 7 | 2,653 | 8,695 | 590 | 232 |
| 8 | 1,720 | 10,273 | 520 | 143 |
| 9 | 1,869 | 9,150 | 414 | 110 |
| 10 | 2,994 | 8,572 | 310 | 142 |
| 11 | 454 | 4,746 | 1,304 | 174 |
| 12 | 202 | 8,947 | 216 | 43 |

## Reduction candidates and their costs

Savings below are **not additive**. Sizes of SQL layout experiments come from
copying the original databases, rewriting the indicated tables and running
`VACUUM`. This holds content constant, and does not establish a runtime speedup.
Negative savings mean growth. `VACUUM` alone provides the control.

For an unimplemented candidate, the tail estimate is deliberately a bound, not
an invented measurement: assume the measured baseline 140.22 ms tail scaled
linearly with the fraction of total bytes removed. This is optimistic because
open/schema costs do not scale with payload bytes, and ignores added read/write
CPU. A range starting at zero means there may be no improvement. Compression
has an actual end-to-end measurement instead.

| Candidate | Application saving | tests/tests saving / evidence | Estimated or measured tail saving | Cost / disposition |
| --- | ---: | --- | --- | --- |
| Drop unread columns | 0 B | No unread column found | 0 ms | Every column has a reader listed above. Not applicable. |
| Drop the second raw signature entirely | 12,580,442 logical B (25.28%) | 1,726,020 B in root package | Invalid estimate: readers need it | Main and raw signatures are different representations. `internalize_pers_struct` / `raw_signature` preserve alias-scraping and genType behavior. Cannot drop. |
| Store an equal raw signature as a reference to the main one | 963,711 logical B (1.94%), less tag overhead | 249,407 B, 413 of 718 root rows; application 1,118 of 3,735 rows | 0–2.72 ms before equality checking and decoding cost | Exact byte comparison, not semantic equality. Needs a new wire tag and lazy reader reconstruction. Below the quarter-size threshold. |
| Derive item digests from decoded stored interfaces | At most 2,244,608 allocated B (4.51%) | 229,376 allocated B | 0–6.33 ms, before root-page retention | Avoids the item rows but requires decoding/hashing providers on incremental reads. The stored-interface hash and whole-interface digest cannot be substituted for item digests. Below threshold. |
| Derive dependency references / warnings by parsing or typechecking sources | Not safely free; deps table is 1,097,728 B (2.21%) | deps table 81,920 B | 0–3.09 ms for deps alone, before added work | Planning needs the graph even for untouched modules. Warning regeneration can require typechecking unchanged modules. Historical mtimes, paths and success state cannot be derived from current sources. Not selected. |
| Compress interface cores independently with safe LZ4 | **22,593,536 allocated B (45.41%)** | Root database 4,849,664 → 1,835,008 B in offline experiment | **12.61 ms median measured**; not half the tail | Actual full-build instruction count rises **0.918%** (minimum of three per side), exceeding +0.1%. Rejected. |
| Also compress extras | 615,102 logical B (1.24%), before page effects | Empty in tests/tests | 0–1.73 ms before compressor cost | Ratio 0.5513; cores alone already fail the instruction gate. Cannot recover the instruction budget by adding compression. |
| Compress reads / items / imports text separately | 976,941 / 363,263 / 270,231 logical B (1.96% / 0.73% / 0.54%) | Much smaller than cores | 0–2.75 / 0–1.02 / 0–0.76 ms before compressor cost | Ratios 0.7905 / 0.7934 / 0.9007: mostly digests and keys. Additional compression work for small savings. |
| `WITHOUT ROWID` for reads and items | **−2,981,888 B** (growth to 52,740,096 B) | Root saves 49,152 B for each table | No projected improvement on application | Eliminates indexes, but large rows spill differently in a SQLite index B-tree. Small test rows are misleading. Rejected. |
| `WITHOUT ROWID` for interfaces | **−6,340,608 B** (growth to 56,098,816 B) | Root grows from 4,849,664 to 5,685,248 B | No projected improvement | Large BLOB overflow dominates; removing the small index makes storage worse. Rejected. |
| Merge reads and items into the modules row | **−2,998,272 B** (growth to 52,756,480 B) | Root shrinks to 4,685,824 B | No projected improvement on application | Removes two rows per module but pushes more of each combined row into overflow pages; also brings cold payload beside eagerly read headers. Rejected. |
| Use a rowid table for modules | 1,277,952 B (2.57%), to 48,480,256 B | Not measured on test root | 0–3.60 ms before index/lookup cost | Larger local payload capacity helps the imports column; below threshold. |
| Merge reads/items into modules **and** use rowid | 1,736,704 B (3.49%), to 48,021,504 B | Not measured on test root | 0–4.89 ms before access-pattern cost | Better than merging into the current `WITHOUT ROWID` table, but still small. Cold payloads remain mixed with hot headers. |
| Use rowid for extras | 360,448 B (0.72%), to 49,397,760 B | Empty test extras table | 0–1.02 ms before lookup/index cost | Avoids some overflow at the cost of a primary-key index. Below threshold. |
| Use rowid for every currently `WITHOUT ROWID` table | 114,688 B (0.23%), to 49,643,520 B | Not measured on test root | 0–0.32 ms | Index overhead cancels most large-row savings. |
| Use 4 / 8 / 32 KiB pages | 2,273,280 / 606,208 / −507,904 B (4.57% / 1.22% / growth) | Not measured on test root | 0–6.41 / 0–1.71 / no projected gain ms, before page-I/O cost | Offline sizes 47,484,928 / 49,152,000 / 50,266,112 B. Smaller pages cut slack but greatly increase page count and writes. Below threshold. |
| Compact existing page slack (`VACUUM`) | 278,528 B (0.56%), to 49,479,680 B | Root unchanged | 0–0.78 ms before vacuum work | Adds a whole database rewrite after already writing it; not a useful clean-build optimization. |
| Encode recorded hexadecimal digests as binary u64 | 1,836,539 logical B (3.69%), before new framing | Application has 88,994 import, 88,994 read and 53,418 item digest entries | 0–5.18 ms from bytes alone; formatting CPU saving unmeasured | Measured sum of current hex lengths minus 8 per entry. Would remove formatting/parsing work but needs all three reader encodings changed and new framing; below threshold. |
| Intern module names across table keys | Upper bound: 427,516 logical B (0.86%) for **all** module keys, before dictionary overhead | Each primary-key index totals 65,536 B across packages | 0–1.20 ms before dictionary lookup cost | Adds a dictionary and integer/name translation to every reader/writer. Index roots remain; exact packed-layout saving not established. Below threshold. |
| Skip unchanged package databases | 0 B of the final record; zero clean-build saving | `write_record` already returns before opening when unchanged | 0 ms for clean builds | Already implemented for no-op/unchanged records; clean builds must persist every compiled package. |
| Copy a prepared empty schema image | 0 B of the final record | Schema pages still required | At most the schema component, not the insert/commit component | Must not replace an open SQLite database or race its rollback journal. Requires an exclusively new-file protocol; no custom lock on SQLite's file. Not implemented. |
| Disable synchronous writes before schema creation | 0 B of the final record | Currently OFF is set only after schema creation | Schema-only probe below saves 120.4 ms summed over twelve serial creates; compiler tail saving unmeasured | Consistent with reconstructible-cache durability, but it is not a size reduction. Not implemented in this inventory-only result. |

The main and raw encoded signatures account for 13,690,879 and 12,580,442 bytes
of the application's 27,930,991 core bytes. Only 963,711 raw bytes are exactly
equal to the main signature in the same row. The raw-signature reader uses
pre-substitution structure; treating all of it as a duplicate would remove
information a reader actually consumes.

**Size conclusion:** no measured, eligible reduction reaches one quarter of the
record. Lossless compression reaches the byte threshold but fails the mandatory
instruction budget and the half-tail target. Removing indexes, attractive on tests/tests, grows the application record;
the best measured merged-row layout saves only 3.49%. The inventory-only stopping condition is supported for size reductions:
do not ship the compressor, change schema 22, or drop/derive any field. The
complete tail decomposition below separately identifies time reductions that
would save no record bytes; no such implementation is claimed here. This is not a claim that no future representation
redesign could improve it.

## Compression probe

The probe uses `lz4_flex` 0.11.6 with default features disabled and `std`,
`safe-encode`, `safe-decode` enabled. Each SQL BLOB is compressed independently
with `compress_prepend_size`, then round-tripped with
`decompress_size_prepended`. No unsafe code or dictionary shared between rows.
The 4-byte uncompressed-length prefix is included in compressed byte counts.
A temporary compiler experiment changes only schema 22 → 23, adds this dependency,
compresses each core in `write_record` immediately before its insert, and
inflates it in `InterfaceCores::read`. It does not move writing or encoding into
the compile window. None of these experimental changes are retained in the PR.

| Input | Rows | Raw B | Packed B | Packed/raw | Compress instructions/MB | Decompress instructions/MB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| tests/tests root cores | 718 | 3,752,204 | 961,011 | 0.2561 | 13,011,604 | 3,963,871 |
| Application cores | 3,735 | 27,930,991 | 7,699,913 | 0.2757 | 13,527,749 | 4,457,703 |

Instructions are Cachegrind `--cache-sim=no` counts: subtract a zero-iteration
run from a ten-iteration run, divide by ten and by uncompressed decimal MB.
Both runs load the same length-prefixed blobs and perform identical setup and
round-trip verification, so startup and setup compression cancel. This measures
the codec plus result allocation/freeing, not SQLite insertion. Whole-build
counts below include the latter as well.

Hyperfine, nine runs of 100 codec iterations on the root test cores:

| Operation | Mean ± standard deviation | Min–max |
| --- | --- | --- |
| Compress | 354.9 ± 23.7 ms | 320.1–408.9 ms |
| Decompress | 93.5 ± 6.4 ms | 88.1–105.7 ms |

These process timings include input loading and initial compression/round-trip
validation once; divide the loop cost, not the entire process time, to estimate
per-record codec cost. They are not application build timings.

## Whole-build instruction rejection

Clean tests/tests builds, one worker, ordinary fat-LTO release binaries,
Cachegrind `--cache-sim=no`; alternate baseline and the temporary compressed-core
experiment, three runs each. Both compile 724 modules.

| Run | Baseline instructions | Compressed-core instructions |
| --- | ---: | ---: |
| 1 | 4,341,650,812 | 4,468,591,433 |
| 2 | 4,340,866,866 | 4,384,182,138 |
| 3 | 4,341,410,098 | 4,380,711,133 |

Minimum-to-minimum: **+0.917887%**, against the maximum **+0.1%**. Even ignoring
the unusually high first candidate run does not change the rejection. These
local exploratory builds use the normal release profile; the CI gate's own
build configuration remains authoritative for shipped changes. The final PR
changes documentation only, so it does not request an instruction-budget waiver.

## Initial application clean-build comparison (project write set only)

This initial run had source copies of runtime/Belt but had not separately
built the runtime database, so record bytes cover only the 12 project databases.
Nine alternating baseline / compressed-core pairs, eight workers, both invoked
from the application directory. Each run is cleaned before timing; the timer
starts before process launch, records the `Finished compilation` line, and ends
after process exit. Linux `/usr/bin/time` supplies peak RSS. No timing probe is
enabled in these binaries. This is the **rejected experimental compressor**, not
a shipped schema change. Values are medians [minimum, maximum].

| Metric | Baseline | Compressed cores |
| --- | ---: | ---: |
| Start → result (ms) | 1,870.06 [1,790.95, 2,103.50] | 1,887.51 [1,782.07, 2,185.45] |
| Start → exit (ms) | 2,019.18 [1,901.64, 2,244.40] | 2,005.95 [1,898.90, 2,322.06] |
| Result → exit (ms) | 140.22 [110.69, 172.08] | 127.62 [111.19, 164.73] |
| Peak RSS (KiB) | 1,241,340 [1,206,420, 1,250,820] | 1,230,080 [1,211,824, 1,243,000] |
| Record bytes | 49,758,208 [49,758,208, 49,758,208] | 27,164,672 [27,164,672, 27,164,672] |

The record is 54.59% of its baseline size, missing the ≤50% target. The median
tail is 91.01% of baseline, missing its ≤50% target by much more. Median result
time is 17.45 ms later; the broad overlapping ranges do not establish that
compilation became slower, but they do not establish the required no-delay
win either. Medians of independently measured phases need not sum. The target
macOS machine was not available in this environment; its coordinator repeat
is not claimed here.

## Schema-only experiment

A Python SQLite microbenchmark creates twelve fresh databases, with the exact
schema and 16 KiB pages, on each invocation. It either uses the current sequence
(schema transaction first, then `synchronous=OFF`), sets OFF before that
transaction, or creates a fresh empty template and copies it twelve times before
opening the copies. Template creation is included. All paths are new temporary
files: this does **not** demonstrate safe replacement of live package databases.
The Python/system SQLite version and serialized execution also differ from the
compiler's bundled SQLite / parallel package writes. Hyperfine, nine runs:

| Strategy | Mean ± standard deviation | Min–max |
| --- | --- | --- |
| Schema then OFF | 177.3 ± 20.4 ms | 149.0–218.2 ms |
| OFF then schema | 56.9 ± 15.8 ms | 39.9–85.4 ms |
| Fresh empty-image copies | 44.8 ± 4.7 ms | 37.6–51.5 ms |

This isolates a real fixed-cost opportunity but saves **zero record bytes**. It
does not justify promising 120 ms off the parallel application's tail, and it
does not satisfy the quarter-size stopping criterion. No production schema
initialization or file-publication protocol is changed.

## Application database 13: separately prepared runtime

The benchmark script builds this before the timed project build. It contains
113 compiled modules and occupies **2,949,120 bytes** (5.60% of the
complete 52,707,328-byte record). It is not opened/written by the measured
application clean build, so its application-tail write costs are zero, not
missing timing samples. Percentages here use the complete record total.

| Object | Rows | Pages | Allocated bytes | Total share | Payload bytes | Unused bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| deps | 158 | 1 | 16,384 | 0.031% | 13,141 | 2,745 |
| interface_extras | 0 | 1 | 16,384 | 0.031% | 0 | 16,376 |
| interfaces | 113 | 160 | 2,621,440 | 4.974% | 2,422,718 | 196,731 |
| items | 113 | 7 | 114,688 | 0.218% | 83,663 | 30,379 |
| meta | 10 | 2 | 32,768 | 0.062% | 7,468 | 25,253 |
| modules | 113 | 1 | 16,384 | 0.031% | 14,000 | 1,987 |
| parse_warnings | 0 | 1 | 16,384 | 0.031% | 0 | 16,376 |
| reads | 113 | 1 | 16,384 | 0.031% | 12,343 | 3,549 |
| runtime_interfaces | 0 | 1 | 16,384 | 0.031% | 0 | 16,376 |
| sources | 158 | 1 | 16,384 | 0.031% | 6,543 | 9,359 |
| sqlite_autoindex_interfaces_1 | — | 1 | 16,384 | 0.031% | 2,327 | 13,710 |
| sqlite_autoindex_items_1 | — | 1 | 16,384 | 0.031% | 2,327 | 13,710 |
| sqlite_autoindex_reads_1 | — | 1 | 16,384 | 0.031% | 2,327 | 13,710 |
| sqlite_schema | — | 1 | 16,384 | 0.031% | 1,469 | 14,750 |
| Free-list | — | 0 | 0 | 0% | — | — |

| Column | Rows | Non-NULL | Logical length B | Total share (logical) |
| --- | ---: | ---: | ---: | ---: |
| meta.key | 10 | 10 | 165 | 0.0003% |
| meta.value | 10 | 10 | 7,270 | 0.0138% |
| sources.path | 158 | 158 | 3,531 | 0.0067% |
| sources.module | 158 | 158 | 2,538 | 0.0048% |
| modules.module | 113 | 113 | 1,876 | 0.0036% |
| modules.js_confirmed_at | 113 | 113 | 2,147 | 0.0041% |
| modules.implementation_warnings | 113 | 0 | 0 | 0.0000% |
| modules.interface_warnings | 113 | 0 | 0 | 0.0000% |
| modules.interface_digest | 113 | 113 | 2,182 | 0.0041% |
| modules.imports | 113 | 113 | 9,455 | 0.0179% |
| parse_warnings.source | 0 | 0 | 0 | 0.0000% |
| parse_warnings.text | 0 | 0 | 0 | 0.0000% |
| deps.source | 158 | 158 | 3,328 | 0.0063% |
| deps.mtime | 158 | 158 | 3,002 | 0.0057% |
| deps.deps | 158 | 158 | 7,560 | 0.0143% |
| deps.gentype_annotations | 158 | 158 | 158 | 0.0003% |
| deps.gentype_declarations | 158 | 158 | 158 | 0.0003% |
| reads.module | 113 | 113 | 1,876 | 0.0036% |
| reads.data | 113 | 113 | 10,052 | 0.0191% |
| items.module | 113 | 113 | 1,876 | 0.0036% |
| items.data | 113 | 113 | 81,334 | 0.1543% |
| interfaces.module | 113 | 113 | 1,876 | 0.0036% |
| interfaces.hash | 113 | 113 | 2,172 | 0.0041% |
| interfaces.data | 113 | 113 | 2,419,312 | 4.5901% |
| interface_extras.module | 0 | 0 | 0 | 0.0000% |
| interface_extras.data | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.module | 0 | 0 | 0 | 0.0000% |
| runtime_interfaces.data | 0 | 0 | 0 | 0.0000% |

## Full-preparation application comparison

After running `scripts/bench_project.sh`, repeat nine alternating baseline /
compressed-core pairs with eight workers. Clean and build each binary's runtime
outside the measured interval, then clean the project and measure its build from
its own directory. This matches the script's preparation and includes all 13
databases in the size total. Same timer and RSS method as above. Values are
medians [minimum, maximum]. No other local heavy build ran concurrently.

| Metric | Baseline | Compressed cores |
| --- | ---: | ---: |
| Start → result (ms) | 2,390.91 [1,504.32, 2,809.30] | 2,486.54 [1,481.72, 2,987.72] |
| Start → exit (ms) | 2,675.49 [1,617.69, 3,001.06] | 2,697.76 [1,588.41, 3,178.45] |
| Result → exit (ms) | 181.01 [113.37, 556.88] | 180.14 [106.69, 246.52] |
| Peak RSS (KiB) | 1,233,636 [1,213,716, 1,239,252] | 1,219,828 [1,204,776, 1,238,688] |
| Record bytes | 52,707,328 [52,707,328, 52,707,328] | 28,147,712 [28,147,712, 28,147,712] |

These runs have substantial host/filesystem variability: they are not evidence
of a small speed difference. They again fail to demonstrate the required
half-size, half-tail and no-later-result combination. The stable evidence for
rejecting the compressor is the instruction increase, not noisy wall time.

The supplied comparison scripts were also run, without skipping instruction
measurement in `bench_project.sh`:

```text
base: files=3980
base: instructions=74340156706 source_lines=656677 instructions_per_line=113206.579
candidate: files=3980
candidate: instructions=74648164791 source_lines=656677 instructions_per_line=113675.620
Outputs identical
Instructions difference: +0.4143%

base: exit code 0, 3735 signatures, 33 diagnostics in 19 files, 3980 generated files
candidate: exit code 0, 3735 signatures, 33 diagnostics in 19 files, 3980 generated files
outcome: both exit with 0
signatures: no difference (3735 compared)
diagnostics: no difference (19 compared)
javascript: no difference (3980 compared)
no differences
```

## Complete tail attribution, including close and non-record work

A second temporary probe instruments the unmodified baseline's control flow,
not the compressor: `result-printed` immediately after the result line;
`record-start` before `UnitDigests::of_compiled`; existing `record-digests`,
`record-written`, `cleanup-end`, `run-main-end` marks; and `before-exit` immediately
before `std::process::exit`. An external parent measures process exit. All probes
are removed from the final tree. `RESCRIPT_PHASE_TIMINGS=1` prints per-database
durations and `RESCRIPT_BUILD_PHASES=1` enables epoch markers. Nine clean builds,
eight workers, runtime prepared outside the measurement.

The instrumented tail median is **105.08 ms** [99.90, 131.11], not the earlier
140.22 ms median. These are different runs on a variable host: do not present
this table as a measured partition of the earlier 140.22 ms. It measures the
same code path and demonstrates which parts that earlier number conflated.

| Interval | Median ms | Min–max ms | What it includes |
| --- | ---: | --- | --- |
| result-printed → record-start | 0.004 | 0.003–0.005 | Dispatch into cleanup / pool selection |
| record-start → record-digests | 1.320 | 1.241–1.522 | Registry snapshot and compiled-unit digest setup |
| record-digests → record-written | 89.433 | 84.655–110.955 | Record construction, SQL encoding, concurrent database writes, local temporary cleanup |
| record-written → cleanup-end | 0.012 | 0.008–0.015 | Return from cleanup |
| cleanup-end → run-main-end | 1.948 | 1.859–2.008 | Root build-lock release, scoped build-thread join, CLI return |
| run-main-end → before-exit | 0.010 | 0.009–0.022 | Telemetry guard drop (telemetry disabled here) |
| before-exit → exit | 10.629 | 9.621–16.839 | Process termination / OS reclamation and parent observation |

Per-database medians, milliseconds. `current_record` is before SQLite and
includes extracting the recorded imports/items/interfaces and building the
record's collections. `metadata/outputs` adds compiler metadata and checks
obsolete output paths. `SQL encode` formats reads/items/imports/dependencies
before opening. `schema/setup` retains the first probe's definition. `close`
explicitly drops the connection **after** the commit timer. `write total` includes
SQL encode through close plus cleanup of encoding temporaries; it overlaps its
component columns. `spawn drop` schedules record destruction on a background
thread; it does not wait for destruction to finish.

| DB | current_record | metadata/outputs | SQL encode | Open | Schema/setup | Inserts | Commit | Close | Write total | Spawn drop |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 31.262 | 0.261 | 6.038 | 0.156 | 1.729 | 25.418 | 23.369 | 0.244 | 57.710 | 0.035 |
| 2 | 2.361 | 0.023 | 1.284 | 0.102 | 3.230 | 5.587 | 4.745 | 0.056 | 15.345 | 0.021 |
| 3 | 0.476 | 0.015 | 0.140 | 0.224 | 5.209 | 3.250 | 1.547 | 0.042 | 10.465 | 0.021 |
| 4 | 0.283 | 0.011 | 0.208 | 0.170 | 5.562 | 2.964 | 0.992 | 0.146 | 10.888 | 0.020 |
| 5 | 0.309 | 0.012 | 0.198 | 0.249 | 5.606 | 1.892 | 1.025 | 0.130 | 9.964 | 0.018 |
| 6 | 0.788 | 0.013 | 0.194 | 0.357 | 4.611 | 2.898 | 0.486 | 0.030 | 8.650 | 0.017 |
| 7 | 0.221 | 0.011 | 0.051 | 0.110 | 5.891 | 0.611 | 0.227 | 0.023 | 7.668 | 0.022 |
| 8 | 0.140 | 0.011 | 0.014 | 0.159 | 5.788 | 0.440 | 0.125 | 0.052 | 6.686 | 0.023 |
| 9 | 0.252 | 0.011 | 0.034 | 0.169 | 5.347 | 0.356 | 0.100 | 0.028 | 6.323 | 0.019 |
| 10 | 0.148 | 0.012 | 0.008 | 0.212 | 5.801 | 0.356 | 0.123 | 0.044 | 6.522 | 0.024 |
| 11 | 0.141 | 0.012 | 0.006 | 0.168 | 4.550 | 0.260 | 0.097 | 0.066 | 5.318 | 0.019 |
| 12 | 0.537 | 0.011 | 0.004 | 0.228 | 5.394 | 0.328 | 0.054 | 0.168 | 6.919 | 0.022 |
| 13 (runtime) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

The same expanded probe on one clean tests/tests build (milliseconds):

| DB | current_record | metadata/outputs | SQL encode | Open | Schema/setup | Inserts | Commit | Close | Write total | Spawn drop |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 3.858 | 0.191 | 0.828 | 0.193 | 5.873 | 5.341 | 4.687 | 0.104 | 17.211 | 0.051 |
| 2 | 0.216 | 0.031 | 0.114 | 0.223 | 10.680 | 0.556 | 0.224 | 0.060 | 11.958 | 0.055 |

**Interpretation and selection:**

- Database 1 is the critical package. Its record construction is about 31 ms;
  its SQL write total is about 58 ms, including approximately 6 ms of text
  encoding, 25 ms of inserts and 23 ms of commit. Connection close is 0.24 ms,
  not the missing tail. Medians are not additive exact partitions.
- The small databases' schema costs overlap the dominant package's preparation
  and writes. Summing all package schema times and subtracting that sum from
  elapsed tail time is invalid. The schema-image/OFF microbenchmark above is
  not evidence for halving this application's tail; the main package's schema
  cost is only about 1.7 ms in this probe.
- Roughly 13 ms after record persistence is **not record writing**: root-lock
  release / build-thread join / CLI return and process termination. `main.rs`
  deliberately `forget`s the one-shot build state; it does not synchronously
  free the whole compiler graph. There is no after-build command in this test.
  `clean::drop_in_background` frees per-package records without a join; those
  threads may still be running when the process exits. Do not attribute OS
  teardown or this concurrent work to SQLite commit.
- Compression attacks the insert/commit part while adding codec work; it does
  not remove `current_record` construction, text encoding, or process exit.
  That explains why a 45% project-record size reduction yields a much smaller
  tail change. Both measured instruction counts reject it independently of
  wall-clock noise.
- Choose **no production reduction** from this inventory under the task's
  quarter-size stopping condition. Equal-signature references, binary/key
  packing, page-size and row-layout changes do not establish that size saving;
  schema setup and close are not the dominant critical-path costs. Nothing is
  dropped, no lazy reader changes, and schema 22 remains intact. The precise
  contents of `current_record`'s 31 ms are not a measured subprofile here, so
  no claim is made that a particular transformation would eliminate it.
