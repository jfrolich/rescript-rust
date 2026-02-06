//! Parser performance benchmarks: Rust bsc vs OCaml bsc (exe-vs-exe).
//!
//! Both compilers run as subprocesses with `bsc -bs-ast -o <tmpfile> <input.res>`.
//! This measures the full parse-to-binary-AST pipeline as seen by the build system.
//!
//! Paths are relative to the `compiler-rust/` directory (where Cargo.toml lives),
//! since `cargo test` sets the working directory to the package root.

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::time::{Duration, Instant};

    /// Path to the Rust bsc binary (release build), relative to compiler-rust/
    const RUST_BSC: &str = "target/release/bsc";

    /// Path to the OCaml bsc binary, relative to compiler-rust/
    const OCAML_BSC: &str = "../_build/install/default/bin/bsc";

    /// Number of iterations per benchmark
    const ITERATIONS: u32 = 50;

    /// Maximum allowed slowdown factor (Rust time / OCaml time).
    /// 1.0 means Rust must be at least as fast as OCaml.
    const MAX_SLOWDOWN_FACTOR: f64 = 1.0;

    /// Base path for test files, relative to compiler-rust/
    const TEST_BASE: &str = "../tests/syntax_tests/data";

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

    /// Benchmark a single source file: run both bsc binaries ITERATIONS times,
    /// return (rust_avg, ocaml_avg) durations.
    fn benchmark_file(source_file: &Path) -> Option<(Duration, Duration)> {
        let tmp_dir = tempfile::tempdir().ok()?;
        let rust_out = tmp_dir.path().join("rust.ast");
        let ocaml_out = tmp_dir.path().join("ocaml.ast");

        // Warm up (1 run each)
        run_bsc(RUST_BSC, source_file, &rust_out)?;
        run_bsc(OCAML_BSC, source_file, &ocaml_out)?;

        // Benchmark Rust bsc
        let mut rust_total = Duration::ZERO;
        for _ in 0..ITERATIONS {
            rust_total += run_bsc(RUST_BSC, source_file, &rust_out)?;
        }

        // Benchmark OCaml bsc
        let mut ocaml_total = Duration::ZERO;
        for _ in 0..ITERATIONS {
            ocaml_total += run_bsc(OCAML_BSC, source_file, &ocaml_out)?;
        }

        Some((rust_total / ITERATIONS, ocaml_total / ITERATIONS))
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
            "  {:<40} {:>8} {:>10.0}us {:>10.0}us {:>7.2}x  {}",
            name, size, rust_us, ocaml_us, factor, status
        );
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
    // Grammar expression benchmarks (small-medium files)
    // ========================================================================

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

    // ========================================================================
    // Real-world idempotency benchmarks (large files, 20-60KB)
    // ========================================================================

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
    // Comprehensive benchmark (all files, ignored by default)
    // ========================================================================

    #[test]
    #[ignore] // Run with: cargo test --release --lib -- benchmark_all --ignored --nocapture
    fn benchmark_all() {
        if !binaries_available() {
            eprintln!(
                "Skipping benchmarks: one or both bsc binaries not found\n  Rust:  {}\n  OCaml: {}",
                RUST_BSC, OCAML_BSC
            );
            return;
        }

        let files: &[(&str, &str)] = &[
            // Grammar expressions
            ("grammar/regex", "parsing/grammar/expressions/regex.res"),
            ("grammar/arrow", "parsing/grammar/expressions/arrow.res"),
            ("grammar/if", "parsing/grammar/expressions/if.res"),
            ("grammar/UncurriedByDefault", "parsing/grammar/expressions/UncurriedByDefault.res"),
            ("grammar/block", "parsing/grammar/expressions/block.res"),
            ("grammar/constants", "parsing/grammar/expressions/constants.res"),
            ("grammar/record", "parsing/grammar/expressions/record.res"),
            ("grammar/binary", "parsing/grammar/expressions/binary.res"),
            ("grammar/array", "parsing/grammar/expressions/array.res"),
            ("grammar/switch", "parsing/grammar/expressions/switch.res"),
            ("grammar/async", "parsing/grammar/expressions/async.res"),
            ("grammar/firstClassModule", "parsing/grammar/expressions/firstClassModule.res"),
            // Real-world idempotency files
            ("idempotency/ReactDOMRe", "idempotency/reason-react/src/ReactDOMRe.res"),
            ("idempotency/Css_Legacy_Core", "idempotency/bs-css/Css_Legacy_Core.res"),
            ("idempotency/Arnold", "idempotency/genType/src/Arnold.res"),
            ("idempotency/index", "idempotency/ludum-dare-46/index.res"),
            ("idempotency/EmitJs", "idempotency/genType/src/EmitJs.res"),
        ];

        println!("\n{:-<90}", "");
        println!(
            "  {:<40} {:>8} {:>10} {:>10} {:>7}",
            "Test", "Size", "Rust", "OCaml", "Factor"
        );
        println!("{:-<90}", "");

        let mut results: Vec<(&str, f64)> = Vec::new();
        let mut failures: Vec<(&str, f64)> = Vec::new();

        for &(name, relative_path) in files {
            let source_file = test_path(relative_path);
            if !source_file.exists() {
                eprintln!("  {:<40} SKIPPED (file not found)", name);
                continue;
            }

            let size = std::fs::metadata(&source_file).map(|m| m.len()).unwrap_or(0);

            match benchmark_file(&source_file) {
                Some((rust_avg, ocaml_avg)) => {
                    let rust_us = rust_avg.as_nanos() as f64 / 1000.0;
                    let ocaml_us = ocaml_avg.as_nanos() as f64 / 1000.0;
                    let factor = rust_us / ocaml_us;

                    print_result(name, size, rust_us, ocaml_us, factor);
                    results.push((name, factor));

                    if factor > MAX_SLOWDOWN_FACTOR {
                        failures.push((name, factor));
                    }
                }
                None => {
                    eprintln!("  {:<40} FAILED (benchmark error)", name);
                }
            }
        }

        println!("{:-<90}", "");

        let passing = results.iter().filter(|(_, f)| *f <= MAX_SLOWDOWN_FACTOR).count();
        let faster = results.iter().filter(|(_, f)| *f < 1.0).count();
        let total = results.len();

        println!(
            "  Results: {}/{} passing, {}/{} faster than OCaml",
            passing, total, faster, total
        );

        if !failures.is_empty() {
            println!("\n  Failures:");
            for (name, factor) in &failures {
                println!("    {} is {:.2}x slower than OCaml", name, factor);
            }
            panic!(
                "{} benchmark(s) failed - Rust bsc is too slow (max allowed: {:.2}x)",
                failures.len(),
                MAX_SLOWDOWN_FACTOR
            );
        }
    }
}
