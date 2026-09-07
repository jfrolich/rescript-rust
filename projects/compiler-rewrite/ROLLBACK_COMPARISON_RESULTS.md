# Rollback comparison results

The fixed comparison completed all 32 timed builds with no failed slots. The two qualification builds and every timed build compiled 3,248 modules and produced 5,048 JavaScript files with digest `1cacd5cfb9604df30e204f3d8a419e4e433afa96e3f81d23ea54764af86f1d49`. M and R had no per-file output differences. Input, source, symlink, binary, and generated-file restoration checks passed.

The authoritative inner whole-process wall samples were:

| mode | variant | n | mean | SD | min | max |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| w12 | current main M | 8 | 4.7759 s | 0.0393 s | 4.7221 s | 4.8423 s |
| w12 | rollback R | 8 | 5.0576 s | 0.0476 s | 4.9863 s | 5.1311 s |
| w1 | current main M | 8 | 20.2464 s | 0.1136 s | 20.1489 s | 20.4849 s |
| w1 | rollback R | 8 | 21.7880 s | 0.2698 s | 21.4605 s | 22.1757 s |

At w12, paired R minus M averaged +0.2817 s with SD 0.0768 s and a 95% t interval of [+0.2175, +0.3459] s. R was 5.90% slower by cell means. At w1, paired R minus M averaged +1.5415 s with SD 0.2548 s and a 95% t interval of [+1.3285, +1.7546] s. R was 7.61% slower by cell means. R was slower in all eight pairs in both modes.

The primary w12 result rejects a performance reason to retain the rollback. The separate w1 result points the same way. Output correctness was identical, and current main retains the already verified fixes. The recommendation is not to merge the aggregate rollback PR and to keep current main. This conclusion does not use the historical A comparison.

## Supervision record

The shell tool that launched the one timed runner stopped waiting after its 600-second tool limit. It did not terminate the existing `lockf` and Python runner. At that point the same process IDs were still active, with 28 attempted slots and 27 finalized rows. I did not start a second timed invocation. I polled that same Python process until it exited, then observed 32 attempted slots and 32 finalized rows. All 32 per-build bounded process and Hyperfine records have successful exits, required metrics, and matching output manifests. The final inventory and restoration checks passed. The top-level runner's exit status was not observable after it became detached, so this report does not claim it exited zero. No measurement or lock processes remained afterward, and the heavy lock was available.

Raw evidence is in `/Users/jake/.opensession/artifacts/rescript-performance-20260905/rollback-comparison`. `summary.json` has SHA-256 `5958ab9df9b25e12c5a239febc18f9822877d2a4015e863fabfd10dd3e00c747`; `plan.json` has SHA-256 `ca8e667fb7067cf169e6d32bc807ffb21ba74133459cd7a27f572dae4ee2b30e`; `qualification-report.json` has SHA-256 `3f8776c62d4cd114d0afac8fafa67de5d4e49ed98e028c260019bba7f922e2e7`.
