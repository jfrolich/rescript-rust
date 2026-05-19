# Beta Cleanup Review Plan

## Scope

This project tracks cleanup work before a beta release from the
`ocaml-to-rust-rewrite` branch.

Review base:
- Upstream base: `0a51c27b718bb8e49d88cd570d1dc6dcfba627f9`
- Reviewed head: `22e9d4247dd416989df8672cc201b068ec5b4a5c`
- Diff size: 2,103 changed paths, 548,166 insertions, 768 deletions

This is a release-readiness audit, not a parity implementation project. The
current pass records problems and decisions to make before beta. It does not
try to fix parity by normalization or Rust-only compatibility layers.

## Review Method

1. Compare the full branch diff against `upstream/master`.
2. Classify every changed path by status and top-level area.
3. Review added files for generated artifacts, local paths, symlinks, debug
   leftovers, one-off migration scripts, incomplete implementations, and release
   packaging impact.
4. Review modified release-facing files: package manifests, workflows, build
   scripts, OCaml reference debug hooks, Rust compiler driver, and rewatch.
5. Record findings as release blockers, must-review items, or follow-up cleanup.

## Release Cleanup Workstreams

1. Packaging and executable surface
   - Verify npm package `bin` entries point at files included in the package.
   - Verify `packages/artifacts.json` agrees with `package.json`.
   - Run dry-pack inspection before beta.

2. Generated and machine-local files
   - Remove local caches, generated build metadata, local symlinks, and absolute
     machine paths unless they are deliberately versioned release assets.
   - Keep generated snapshots only when there is a documented upstream policy.

3. Debug and instrumentation leftovers
   - Remove unconditional debug writes and temporary tracing.
   - For optional debug flags, avoid hot-path environment parsing in release code
     unless cached.

4. Portability
   - Replace hard-coded platform paths and personal checkout paths in scripts.
   - Ensure debug-build defaults remain the iteration default.

5. Rust safety and incomplete paths
   - Review new `unsafe` blocks against repository policy.
   - Replace user-reachable `unimplemented!` or temporary panics before beta.

6. Test fixtures
   - Confirm deleted fixtures are not still imported.
   - Preserve test semantics where symlink fixtures were meant to exercise
     symlink behavior.

## Acceptance Gates Before Beta

- `npm pack --dry-run` includes every file referenced by `package.json` `bin`.
- No tracked absolute symlink points to a developer machine path.
- No tracked `lib/bs` build artifacts or `.performance-cache` files unless
  intentionally documented as release fixtures.
- No unconditional `/tmp` debug outputs from compiler code.
- No user-facing GenType path reaches `unimplemented!`.
- Debug builds succeed for `compiler-rust` and `rewatch`.
- Existing parity smoke scripts run from the repo root using debug artifacts.
