# Rollback comparison protocol

This comparison measures current main, M, against the rollback PR, R. It is separate from the closed Env ownership cohort. M is the preserved coherent release pair built from `a59f271c7437b9b6f3568cab44b56851f079a07a`, with docs-only commits through main `d98b8b9430045d40d08ed89dd75174b5669fa829`. R is the preserved release pair built from rollback source `24875256e`, with docs-only commits through `65a3f342f385580134aeb0e1a539e4db5032f2c5`. M is not the lost `7f` binary or the `88` candidate.

The protocol first runs two separate untimed qualification builds at 12 workers, M then R. Both must compile 3,248 modules, produce 5,048 JavaScript files, match each other byte for byte, and match digest `1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49`. Failure stops the timed plan. Qualification timing is diagnostic only.

If qualification passes, eight pairs run at 12 workers and eight at one worker, 32 builds total. Odd pairs use mode order w12 then w1 and variant order MR. Even pairs use w1 then w12 and RM. Each slot gets a full clean outside timing. Hyperfine runs once with no warmup. The authoritative sample is `perf_counter_ns` around `/usr/bin/time -lp` plus `rescript build --in-process --no-timing true`. There are no retries, replacements, exclusions, extensions, screen pool, or seed search.

Both variants use `/Users/jake/checkouts/rescript-rust/packages/@rescript/runtime`. The runner records process metrics, load, exits, counts, and a JavaScript manifest for every build. It freezes reachable inputs, both tracked compiler trees, symlinks, and copied and original binaries. Only the exact 12 known generated metadata paths may appear after a build. The 18 pre-existing generated TypeScript files are checked against preserved originals, copied to a new backup, and restored even on failure.

All compiler executions run under `/usr/bin/lockf -k /tmp/rescript-tella-heavy.lock`. Clean is bounded at 120 seconds, builds at 180 seconds, and each outer Hyperfine process group at 210 seconds. Evidence stays in `/Users/jake/.opensession/artifacts/rescript-performance-20260905/rollback-comparison`.
