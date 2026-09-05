# Fresh production rebaseline (542)

## Preregistered protocol — before timings

Compare A: archived `fb4497659fdf53b491fc5480d6588ec800e92e0a` with B: `542b505076e73552325566d45116f5d2d9b60024` compiler/rewatch source (HEAD `0af66c28b` differs only in campaign documentation). No indexed activation or optimization edits. Historical executables are missing; rebuild both with current identical Rust toolchain, default features, release profiles, unset RUSTFLAGS. This tests source stacks under today's toolchain, not identity with historical executable hashes.

Artifact root: `/tmp/rescript-measure-rebaseline-542`. Historical sources are a git archive, not a worktree. Save immutable binaries, hashes and raw logs there. All heavy commands hold `/tmp/rescript-tella-heavy.lock` via `lockf -k`.

Fixed corpus: Tella `66a5edabdbfdbc5dd7496e59ee0573de2a2a1ffa`, webapp directory `/Users/jake/dev/tella-fusion/packages/core/webapp`. Fixed runtime: this campaign worktree's `packages/@rescript/runtime`. Save exact backups and SHA-256 of the 18 pre-existing generated TypeScript modifications before building. Hash tracked source/config/lockfiles before/after; generated files are excluded from source invariance checks. Verify 3,248 compiled modules and a 5,048-file JS content manifest (outside node_modules) on each authoritative run. A different count or failed build is invalid and stops the run; retain failures. Output differences between stacks must be reported, not normalized away.

Clean policy: run the selected executable's `clean <webapp>` before each build, outside timing. Build command: `build --in-process --no-timing true <webapp>`, explicit RESCRIPT_BSC_EXE, RESCRIPT_RUNTIME and RAYON_NUM_THREADS. Do not clear OS filesystem caches or change runtime policy between variants. Initial screening warms filesystem caches. Clean is compiler-artifact clean, not cold disk/cache benchmarking.

Preset samples:
1. Hyperfine screening: 2 runs per stack/mode at w1/w12, cleanup in prepare. Not acceptance evidence.
2. Authoritative: 8 pairs per mode, w1 then w12 on odd pairs, reversed on even pairs; AB on odd pairs, BA on even pairs. `perf_counter_ns` encompasses the complete build process plus `/usr/bin/time -lp` wrapper; clean and manifest hashing excluded. Record CPU, RSS, raw OS metrics, status and manifests. No extending samples in response to significance. Report paired B-minus-A mean and 95% Student-t interval, plus mean/SD/median/range.
3. Scaling: faster valid w12 source stack, 3 runs each at 1/2/4/6/8/10/12/16, orders ascending, descending, ascending. Hardware is Apple Mac16,10, 4 performance + 6 efficiency cores; worker count is not equivalent CPU capacity. Separate knee confirmation: 4 alternating pairs of minimum-mean screen worker count versus 12 (versus 10 if winner is 12). No interpretation of oversubscription as homogeneous-core efficiency.
4. Separate fresh serial and parallel profiles on the faster valid stack, built-in phase/module/scheduler metrics, OS sampling and mimalloc statistics. Preserve raw outputs; do not count overlapping sampled stacks as additive savings or aggregate thread wall as elapsed time. Missing allocation/counter evidence remains a limitation. No production optimization in this session.

Machine at registration: macOS 15.6 (24G84), rustc/cargo 1.93.1, LLVM 21.1.8, Node 22.22.0, AC power; load 2.95/2.61/2.47. Xcode CommandLineTools selected. Record per-run load and power/thermal snapshots where available; do not infer bandwidth saturation from IPC or RSS alone.

Results and ranked experiments pending execution.
