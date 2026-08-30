# Package Signature Store Plan

## Goal

Store all reusable in-process signatures for a package in one package-local binary file so clean and incremental builds can seed `ModuleRegistry` without reading many `.cmi` files or recompiling stable package sources.

The first target is `@rescript/runtime`: after the runtime has been compiled once, a later clean in-process build should load the runtime signature store and skip runtime source compilation. The same mechanism should later apply to dependency packages and then project-package incremental updates.

## Location

Use the package's existing build artifact directory so the file is naturally ignored by projects that already ignore ReScript build output.

Current code note: `rewatch/src/build/packages.rs` defines `Package::get_build_path()` as:

```text
<package>/lib/bs
```

The user-facing proposal was `<package>/bin/bs`. Before implementation, make this an explicit product decision:

- If the intended directory is the existing ReScript build artifact directory, use `Package::get_build_path()` and place the file under `<package>/lib/bs`.
- If we intentionally want a new literal `<package>/bin/bs` location, add a dedicated helper such as `Package::get_signature_store_path()` and ensure package creation/clean/watch logic knows about that directory.

Recommended first implementation: use `Package::get_build_path()` to avoid introducing a second build-output root. The file name can be:

```text
<package-build-path>/package.rsigpack
```

For namespaced or multi-target packages, include enough config in the header to invalidate incompatible stores rather than multiplying file names early.

## Data Model

The store is a package image for in-process compiler metadata. It is not a replacement for the subprocess `bsc` `.cmi` path.

Store per package:

- package name and package root identity
- compiler ABI/version hash
- relevant config hash
- dependency package signature digests
- module directory
- module exported signatures
- portable type graphs
- module purity
- `.cmj` export constants needed by JS codegen
- alias rewrite metadata
- source/interface content hashes
- signature fingerprints

The natural Rust source types today are:

- `PortablePersStruct`
- `PortableTypeGraph`
- `Signature`
- `InMemoryModuleInfo`
- `CmjExportConstant`
- alias rewrites from `ModuleRegistry`

Do not serialize the whole `ModuleRegistry` shape directly. The on-disk format should be a compact stable package image that can seed the registry.

## Binary Format

Use a custom binary format with explicit tables, not serde-derived recursive structs.

Layout:

1. Header
   - magic: `RSIGPACK`
   - format version
   - compiler ABI hash
   - package name string id
   - config hash
   - dependency digest table offset
   - module directory offset
   - string table offset
   - footer offset or footer search marker

2. String table
   - package-wide string interning
   - module names, labels, constructors, field names, paths, source paths
   - compact varint lengths and UTF-8 bytes

3. Path table
   - compact path node encoding
   - path nodes reference string ids and earlier path node ids
   - avoid repeating nested `Path` trees in every signature item

4. Module directory
   - module name id
   - source hash
   - interface hash if present
   - dependency module ids
   - signature fingerprint
   - purity flag
   - runtime flag
   - offsets/lengths for signature, type graph, JS metadata, alias rewrites

5. Signature/type sections
   - flat indexed encoding of signature items
   - `TypeExprRef` stored as `u32` indices into that module's type graph
   - vectors encoded with compact lengths
   - strings and paths reference package tables

6. JS metadata section
   - `cmj_export_constants`
   - module purity
   - package-relative output/source metadata needed by JS resolution

7. Footer
   - package digest
   - checksum
   - previous footer offset for append-only updates

## Incremental Update Strategy

Use an append-only file:

- a changed module appends new module blobs
- a new module directory/footer is appended last
- readers use the newest valid footer
- stale blobs remain until compaction

This avoids rewriting a large package file for single-module incremental edits.

Compaction policy:

- compact when garbage exceeds a threshold, for example 30-50%
- compact only after a successful build wave
- write compacted image to a temporary file, validate it, then atomically rename

Crash safety:

- never mutate old blobs in place
- footer is the commit record
- if the newest footer is corrupt, fall back to the previous valid footer

## Read Path

Package loading should be lazy.

On build startup:

1. Discover package configs as today.
2. For each dependency package, try loading `package.rsigpack`.
3. Validate header/config/dependency digests.
4. Seed `ModuleRegistry` with package-backed module handles.
5. Do not eagerly deserialize every module into `PortablePersStruct`.

When `PersistentEnv::find_pers_struct` forces a module:

1. Resolve the module handle in `ModuleRegistry`.
2. If it is package-backed, decode only that module's signature/type graph.
3. Internalize into the current `TypeContext`.
4. Cache the internalized `PersStruct` in the existing env-local cache.

Future optimization: internalize directly from package image sections without first constructing a full owned `PortablePersStruct`.

## Write Path

When a module signature is published:

1. Keep the current in-memory publication path unchanged.
2. Record a package-store update containing:
   - module name
   - `PortablePersStruct`
   - `InMemoryModuleInfo`
   - alias rewrites
   - source/interface hashes
   - signature fingerprint
3. At the end of a successful package build wave, append updates to `package.rsigpack`.

For `@rescript/runtime`:

1. If the store is valid, preload it and skip `pre_compile_runtime_modules`.
2. If missing or stale, compile runtime from source as today.
3. After successful runtime compilation, write the store.

## Registry Changes

Add a registry module-handle abstraction:

```text
ModuleRegistryEntry =
  InMemory(Arc<PortablePersStruct>)
  PackageBacked { package_image: Arc<PackageSignatureImage>, module_id: u32 }
```

Keep worker snapshots cheap by sharing package images through `Arc`.

Required changes:

- `compiler-rust/src/cmi/package_store.rs`
- `compiler-rust/src/cmi/persistent_env.rs`
- `compiler-rust/src/cmi/portable_types.rs`
- `rewatch/src/build/compile.rs`
- `rewatch/src/build/packages.rs`
- tests for cache valid/stale/corrupt behavior

## Invalidation

A package store is valid only when these match:

- format version
- compiler ABI hash
- package config hash
- relevant compiler flags
- namespace/package-spec configuration
- dependency package digests
- runtime version/hash for runtime consumers

Per module, validate:

- `.resi` hash if present
- `.res` hash for no-interface modules
- signature fingerprint
- dependency signature fingerprints

If a module implementation changes but its exported signature fingerprint is unchanged, update JS metadata/output but do not invalidate dependents.

## Measurement Gates

Add counters:

- package stores loaded
- stale reason counts
- bytes read
- modules indexed
- modules decoded
- package-backed module cache hits
- runtime source modules skipped
- package load wall time
- package decode/internalize wall time

Benchmarks:

- Tella clean in-process with missing runtime store
- Tella clean in-process with valid runtime store
- Tella clean in-process with dependency package stores
- incremental single-file edit with append-only update

Every retained implementation step must keep:

- Tella build complete
- JS output parity on the current corpus (`610/610` at the latest validation)
- canonical typedtree parity on the current corpus (`610/610` at the latest validation)
- subprocess `bsc` path supported

## Milestones

1. Runtime package store writer.
2. Runtime package store reader and `ModuleRegistry` preload.
3. Lazy package-backed module decoding.
4. Append-only update format with footer validation.
5. Dependency package preload.
6. Project package incremental appends.
7. Direct internalization from package image without owned `PortablePersStruct`.
