//! Parser performance benchmarks: Rust bsc vs OCaml bsc (exe-vs-exe).
//!
//! Both compilers run as subprocesses with `bsc -bs-ast -o <tmpfile> <input.res>`.
//! This measures the full parse-to-binary-AST pipeline as seen by the build system.
//!
//! Paths are relative to the `compiler-rust/` directory (where Cargo.toml lives),
//! since `cargo test` sets the working directory to the package root.
//!
//! ## Running benchmarks
//!
//! ```bash
//! # All files (700+), 10 iterations each — takes ~3 minutes:
//! cargo test --release --lib -- benchmark_all --ignored --nocapture
//!
//! # Individual quick check (50 iterations):
//! cargo test --release --lib -- benchmark_regex --nocapture
//! ```

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::time::{Duration, Instant};

    /// Path to the Rust bsc binary (release build), relative to compiler-rust/
    const RUST_BSC: &str = "target/release/bsc";

    /// Path to the OCaml bsc binary, relative to compiler-rust/
    const OCAML_BSC: &str = "../_build/install/default/bin/bsc";

    /// Number of iterations for individual benchmark tests
    const ITERATIONS: u32 = 50;

    /// Number of iterations for the comprehensive benchmark (lower to keep runtime reasonable)
    const ITERATIONS_ALL: u32 = 10;

    /// Maximum allowed slowdown factor (Rust time / OCaml time).
    /// Slightly above 1.0 to account for subprocess measurement noise.
    /// At ~10ms per run, process startup jitter alone is ±1-2ms (~20%).
    const MAX_SLOWDOWN_FACTOR: f64 = 1.2;

    /// Minimum file size (bytes) for inclusion in comprehensive benchmark.
    /// Files below this threshold produce times dominated by process startup noise.
    const MIN_FILE_SIZE: u64 = 500;

    /// Base path for test files, relative to compiler-rust/
    const TEST_BASE: &str = "../tests/syntax_tests/data";

    /// Directories to exclude (parse errors, stress tests)
    const EXCLUDED_DIRS: &[&str] = &["errors", "recovery", "infiniteLoops"];

    /// Check if both bsc binaries are available and we're running in release mode.
    /// Benchmarks are only meaningful in release mode to avoid subprocess timing noise.
    fn binaries_available() -> bool {
        if cfg!(debug_assertions) {
            return false;
        }
        Path::new(RUST_BSC).exists() && Path::new(OCAML_BSC).exists()
    }

    /// Resolve a test file path relative to the test base
    fn test_path(relative: &str) -> PathBuf {
        Path::new(TEST_BASE).join(relative)
    }

    /// Run a bsc binary on a source file, writing output to a temp file.
    /// Returns the elapsed wall-clock time, or None on failure.
    fn run_bsc(bsc_path: &str, source_file: &Path, output_file: &Path) -> Option<Duration> {
        let start = Instant::now();
        let result = Command::new(bsc_path)
            .arg("-bs-ast")
            .arg("-o")
            .arg(output_file)
            .arg(source_file)
            .output();
        let elapsed = start.elapsed();

        match result {
            Ok(output) if output.status.success() => Some(elapsed),
            Ok(output) => {
                eprintln!(
                    "bsc failed ({}): {}",
                    bsc_path,
                    String::from_utf8_lossy(&output.stderr)
                );
                None
            }
            Err(e) => {
                eprintln!("Failed to run {}: {}", bsc_path, e);
                None
            }
        }
    }

    /// Benchmark a single source file: run both bsc binaries N times,
    /// return (rust_min, ocaml_min) durations.
    ///
    /// Uses the minimum time across iterations rather than the mean.
    /// The minimum is the best estimator for subprocess benchmarks because
    /// OS scheduling noise only adds time, never subtracts it.
    fn benchmark_file_n(source_file: &Path, iterations: u32) -> Option<(Duration, Duration)> {
        let tmp_dir = tempfile::tempdir().ok()?;
        let rust_out = tmp_dir.path().join("rust.ast");
        let ocaml_out = tmp_dir.path().join("ocaml.ast");

        // Warm up (2 runs each to prime caches and page tables)
        run_bsc(RUST_BSC, source_file, &rust_out)?;
        run_bsc(RUST_BSC, source_file, &rust_out)?;
        run_bsc(OCAML_BSC, source_file, &ocaml_out)?;
        run_bsc(OCAML_BSC, source_file, &ocaml_out)?;

        // Benchmark Rust bsc - take minimum
        let mut rust_min = Duration::MAX;
        for _ in 0..iterations {
            let t = run_bsc(RUST_BSC, source_file, &rust_out)?;
            rust_min = rust_min.min(t);
        }

        // Benchmark OCaml bsc - take minimum
        let mut ocaml_min = Duration::MAX;
        for _ in 0..iterations {
            let t = run_bsc(OCAML_BSC, source_file, &ocaml_out)?;
            ocaml_min = ocaml_min.min(t);
        }

        Some((rust_min, ocaml_min))
    }

    /// Benchmark with default iteration count
    fn benchmark_file(source_file: &Path) -> Option<(Duration, Duration)> {
        benchmark_file_n(source_file, ITERATIONS)
    }

    /// Print a benchmark result line
    fn print_result(name: &str, size: u64, rust_us: f64, ocaml_us: f64, factor: f64) {
        let status = if factor <= 1.0 {
            "FASTER"
        } else if factor <= MAX_SLOWDOWN_FACTOR {
            "OK"
        } else {
            "SLOW"
        };
        println!(
            "  {:<70} {:>8} {:>10.0}us {:>10.0}us {:>7.2}x  {}",
            name, size, rust_us, ocaml_us, factor, status
        );
    }

    /// Discover all .res files under TEST_BASE, excluding error/recovery dirs,
    /// filtered to files >= MIN_FILE_SIZE bytes, sorted by size descending.
    fn discover_test_files() -> Vec<(String, PathBuf, u64)> {
        let base = Path::new(TEST_BASE);
        let mut files: Vec<(String, PathBuf, u64)> = Vec::new();

        fn walk_dir(dir: &Path, base: &Path, files: &mut Vec<(String, PathBuf, u64)>) {
            let entries = match std::fs::read_dir(dir) {
                Ok(e) => e,
                Err(_) => return,
            };
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    let dir_name = path.file_name().unwrap_or_default().to_string_lossy();
                    if !EXCLUDED_DIRS.contains(&dir_name.as_ref()) {
                        walk_dir(&path, base, files);
                    }
                } else if path.extension().map_or(false, |e| e == "res") {
                    let size = std::fs::metadata(&path).map(|m| m.len()).unwrap_or(0);
                    if size >= MIN_FILE_SIZE {
                        let rel = path.strip_prefix(base).unwrap_or(&path);
                        let name = rel.to_string_lossy().to_string();
                        files.push((name, path, size));
                    }
                }
            }
        }

        walk_dir(base, base, &mut files);
        // Sort by size descending (largest files first)
        files.sort_by(|a, b| b.2.cmp(&a.2));
        files
    }

    /// Macro to generate individual benchmark tests, reducing boilerplate.
    macro_rules! benchmark_test {
        ($test_name:ident, $display_name:expr, $relative_path:expr) => {
            #[test]
            fn $test_name() {
                if !binaries_available() {
                    eprintln!(
                        "Skipping benchmark: one or both bsc binaries not found\n  Rust:  {}\n  OCaml: {}",
                        RUST_BSC, OCAML_BSC
                    );
                    return;
                }

                let source_file = test_path($relative_path);
                if !source_file.exists() {
                    eprintln!("Skipping benchmark: test file not found: {}", source_file.display());
                    return;
                }

                let size = std::fs::metadata(&source_file).map(|m| m.len()).unwrap_or(0);

                let (rust_avg, ocaml_avg) = benchmark_file(&source_file)
                    .expect(&format!("Benchmark failed for {}", $display_name));

                let rust_us = rust_avg.as_nanos() as f64 / 1000.0;
                let ocaml_us = ocaml_avg.as_nanos() as f64 / 1000.0;
                let factor = rust_us / ocaml_us;

                print_result($display_name, size, rust_us, ocaml_us, factor);

                assert!(
                    factor <= MAX_SLOWDOWN_FACTOR,
                    "Rust bsc is {:.2}x slower than OCaml bsc for {} (max allowed: {:.2}x)",
                    factor,
                    $display_name,
                    MAX_SLOWDOWN_FACTOR
                );
            }
        };
    }

    // ========================================================================
    // Individual benchmark tests (50 iterations, for quick regression checks)
    // ========================================================================

    // Grammar expression benchmarks (small-medium files)

    benchmark_test!(
        benchmark_regex,
        "grammar/regex",
        "parsing/grammar/expressions/regex.res"
    );

    benchmark_test!(
        benchmark_arrow,
        "grammar/arrow",
        "parsing/grammar/expressions/arrow.res"
    );

    benchmark_test!(
        benchmark_if,
        "grammar/if",
        "parsing/grammar/expressions/if.res"
    );

    benchmark_test!(
        benchmark_uncurried_by_default,
        "grammar/UncurriedByDefault",
        "parsing/grammar/expressions/UncurriedByDefault.res"
    );

    benchmark_test!(
        benchmark_block,
        "grammar/block",
        "parsing/grammar/expressions/block.res"
    );

    benchmark_test!(
        benchmark_constants,
        "grammar/constants",
        "parsing/grammar/expressions/constants.res"
    );

    benchmark_test!(
        benchmark_record,
        "grammar/record",
        "parsing/grammar/expressions/record.res"
    );

    benchmark_test!(
        benchmark_binary,
        "grammar/binary",
        "parsing/grammar/expressions/binary.res"
    );

    benchmark_test!(
        benchmark_array,
        "grammar/array",
        "parsing/grammar/expressions/array.res"
    );

    benchmark_test!(
        benchmark_switch,
        "grammar/switch",
        "parsing/grammar/expressions/switch.res"
    );

    benchmark_test!(
        benchmark_async,
        "grammar/async",
        "parsing/grammar/expressions/async.res"
    );

    benchmark_test!(
        benchmark_first_class_module,
        "grammar/firstClassModule",
        "parsing/grammar/expressions/firstClassModule.res"
    );

    // Real-world idempotency benchmarks (large files, 20-60KB)

    benchmark_test!(
        benchmark_react_dom_re,
        "idempotency/ReactDOMRe",
        "idempotency/reason-react/src/ReactDOMRe.res"
    );

    benchmark_test!(
        benchmark_css_legacy_core,
        "idempotency/Css_Legacy_Core",
        "idempotency/bs-css/Css_Legacy_Core.res"
    );

    benchmark_test!(
        benchmark_arnold,
        "idempotency/Arnold",
        "idempotency/genType/src/Arnold.res"
    );

    benchmark_test!(
        benchmark_index,
        "idempotency/index",
        "idempotency/ludum-dare-46/index.res"
    );

    benchmark_test!(
        benchmark_emit_js,
        "idempotency/EmitJs",
        "idempotency/genType/src/EmitJs.res"
    );

    // ========================================================================
    // Comprehensive benchmark: all .res files (700+), 10 iterations each
    // Run with: cargo test --release --lib -- benchmark_all --ignored --nocapture
    // ========================================================================

    #[test]
    #[ignore]
    fn benchmark_all() {
        if !binaries_available() {
            eprintln!(
                "Skipping benchmarks: one or both bsc binaries not found\n  Rust:  {}\n  OCaml: {}",
                RUST_BSC, OCAML_BSC
            );
            return;
        }

        let files = discover_test_files();
        let total = files.len();
        println!("\nDiscovered {} .res files (>= {} bytes)\n", total, MIN_FILE_SIZE);

        println!("{:-<110}", "");
        println!(
            "  {:<70} {:>8} {:>10} {:>10} {:>7}",
            "Test", "Size", "Rust", "OCaml", "Factor"
        );
        println!("{:-<110}", "");

        struct Result {
            name: String,
            size: u64,
            factor: f64,
        }

        let mut results: Vec<Result> = Vec::new();
        let mut failures: Vec<Result> = Vec::new();
        let mut errors: Vec<String> = Vec::new();

        for (i, (name, path, size)) in files.iter().enumerate() {
            // Progress indicator every 50 files
            if i > 0 && i % 50 == 0 {
                eprintln!("  [{}/{}] ...", i, total);
            }

            match benchmark_file_n(path, ITERATIONS_ALL) {
                Some((rust_min, ocaml_min)) => {
                    let rust_us = rust_min.as_nanos() as f64 / 1000.0;
                    let ocaml_us = ocaml_min.as_nanos() as f64 / 1000.0;
                    let factor = rust_us / ocaml_us;

                    print_result(name, *size, rust_us, ocaml_us, factor);

                    let r = Result {
                        name: name.clone(),
                        size: *size,
                        factor,
                    };
                    if factor > MAX_SLOWDOWN_FACTOR {
                        failures.push(Result {
                            name: name.clone(),
                            size: *size,
                            factor,
                        });
                    }
                    results.push(r);
                }
                None => {
                    println!("  {:<70} {:>8} {:>10} {:>10} {:>7}  SKIP", name, size, "-", "-", "-");
                    errors.push(name.clone());
                }
            }
        }

        println!("{:-<110}", "");
        println!();

        // Aggregate statistics
        let passing = results.iter().filter(|r| r.factor <= MAX_SLOWDOWN_FACTOR).count();
        let faster = results.iter().filter(|r| r.factor < 1.0).count();
        let benchmarked = results.len();

        // Stats by size tier
        let tiers: &[(&str, u64, u64)] = &[
            ("Large (>30KB)", 30_000, u64::MAX),
            ("Medium (10-30KB)", 10_000, 30_000),
            ("Small (1-10KB)", 1_000, 10_000),
            ("Tiny (<1KB)", 0, 1_000),
        ];

        println!("  {:<25} {:>6} {:>8} {:>8} {:>10} {:>10} {:>10}",
            "Size Tier", "Files", "Faster", "OK", "Avg Factor", "Min Factor", "Max Factor");
        println!("  {:-<85}", "");

        for &(tier_name, min_size, max_size) in tiers {
            let tier_results: Vec<&Result> = results.iter()
                .filter(|r| r.size >= min_size && r.size < max_size)
                .collect();
            if tier_results.is_empty() {
                continue;
            }
            let tier_count = tier_results.len();
            let tier_faster = tier_results.iter().filter(|r| r.factor < 1.0).count();
            let tier_ok = tier_results.iter().filter(|r| r.factor >= 1.0 && r.factor <= MAX_SLOWDOWN_FACTOR).count();
            let avg_factor: f64 = tier_results.iter().map(|r| r.factor).sum::<f64>() / tier_count as f64;
            let min_factor = tier_results.iter().map(|r| r.factor).fold(f64::MAX, f64::min);
            let max_factor = tier_results.iter().map(|r| r.factor).fold(f64::MIN, f64::max);

            println!("  {:<25} {:>6} {:>8} {:>8} {:>10.2}x {:>10.2}x {:>10.2}x",
                tier_name, tier_count, tier_faster, tier_ok, avg_factor, min_factor, max_factor);
        }

        println!("  {:-<85}", "");
        println!();

        println!(
            "  Overall: {}/{} passing ({} faster, {} within tolerance), {} skipped",
            passing, benchmarked, faster, passing - faster, errors.len()
        );

        if !failures.is_empty() {
            println!("\n  Failures ({}):", failures.len());
            // Sort failures by factor descending (worst first)
            let mut sorted_failures = failures;
            sorted_failures.sort_by(|a, b| b.factor.partial_cmp(&a.factor).unwrap());
            for r in &sorted_failures {
                println!(
                    "    {:<70} {:>8} {:>7.2}x",
                    r.name, r.size, r.factor
                );
            }
            panic!(
                "{} benchmark(s) failed - Rust bsc is too slow (max allowed: {:.2}x)",
                sorted_failures.len(),
                MAX_SLOWDOWN_FACTOR
            );
        }
    }
}
