//! Parser performance benchmarks.
//!
//! Two benchmark modes:
//!
//! 1. **Subprocess (exe-vs-exe)**: Both Rust and OCaml `bsc` run as subprocesses with
//!    `bsc -bs-ast -o <tmpfile> <input.res>`. Measures the full parse-to-binary-AST
//!    pipeline including process startup overhead.
//!
//! 2. **In-process**: Calls the Rust parser directly as a library function. Measures
//!    file I/O + Latin-1 conversion + parsing without subprocess overhead. Shows
//!    throughput in MB/s and optionally compares against OCaml subprocess times.
//!
//! Paths are relative to the `compiler-rust/` directory (where Cargo.toml lives),
//! since `cargo test` sets the working directory to the package root.
//! If `~/dev/tella-fusion` exists, it is included as an additional benchmark corpus.
//!
//! ## Running benchmarks
//!
//! ```bash
//! # Subprocess: all files, 10 iterations each — takes ~3 minutes:
//! cargo test --release --lib -- benchmark_all --ignored --nocapture
//!
//! # In-process: all files, 50 iterations each — takes ~30 seconds:
//! cargo test --release --lib -- benchmark_all_inprocess --ignored --nocapture
//!
//! # In-process repeated corpus benchmark (single process):
//! RAYON_NUM_THREADS=1 PARSER_BENCH_WARMUP=2 PARSER_BENCH_RUNS=10 \
//!   cargo test --release --lib -- benchmark_cold_repeat --ignored --nocapture
//!
//! # Individual subprocess check (50 iterations):
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

    /// Number of iterations for the comprehensive subprocess benchmark
    const ITERATIONS_ALL: u32 = 10;

    /// Number of iterations for in-process benchmarks (no subprocess overhead, so fast)
    const ITERATIONS_ALL_INPROCESS: u32 = 50;

    /// Maximum allowed slowdown factor (Rust time / OCaml time).
    /// Slightly above 1.0 to account for subprocess measurement noise.
    /// At ~10ms per run, process startup jitter alone is ±1-2ms (~20%).
    const MAX_SLOWDOWN_FACTOR: f64 = 1.2;

    /// Base path for core syntax tests, relative to compiler-rust/
    const TEST_BASE: &str = "../tests/syntax_tests/data";

    /// Extra benchmark corpus under $HOME. Added when the directory exists.
    const TELLA_RELATIVE_TO_HOME: &str = "dev/tella-fusion";

    /// Directories to exclude while recursively walking benchmark corpora.
    const EXCLUDED_DIRS: &[&str] = &[
        "errors",
        "recovery",
        "infiniteLoops",
        ".git",
        "target",
        "_build",
        ".next",
    ];

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

    /// Returns benchmark corpora to scan.
    ///
    /// Always includes TEST_BASE.
    /// Also includes ~/dev/tella-fusion when that directory exists.
    fn benchmark_corpora() -> Vec<(String, PathBuf)> {
        let mut corpora = vec![("syntax_tests".to_string(), PathBuf::from(TEST_BASE))];

        if let Some(home_dir) = std::env::var_os("HOME") {
            let tella = PathBuf::from(home_dir).join(TELLA_RELATIVE_TO_HOME);
            if tella.is_dir() {
                corpora.push(("tella-fusion".to_string(), tella));
            }
        }

        corpora
    }

    /// Returns true if a path contains `/lib/bs` or `/lib/ocaml` as directory segments.
    fn is_duplicate_lib_subtree(path: &Path) -> bool {
        let mut prev_was_lib = false;

        for component in path.components() {
            let name = component.as_os_str().to_string_lossy();
            if prev_was_lib && (name == "bs" || name == "ocaml") {
                return true;
            }
            prev_was_lib = name == "lib";
        }

        false
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

    /// Info about a discovered test file.
    struct TestFile {
        name: String,
        path: PathBuf,
        size: u64,
        lines: u64,
    }

    /// Discover all .res/.resi files under benchmark corpora, excluding ignored dirs,
    /// filtered to files >= MIN_FILE_SIZE bytes, sorted by size descending.
    fn discover_test_files() -> Vec<TestFile> {
        let mut files: Vec<TestFile> = Vec::new();

        fn walk_dir(dir: &Path, base: &Path, corpus_name: &str, files: &mut Vec<TestFile>) {
            let entries = match std::fs::read_dir(dir) {
                Ok(e) => e,
                Err(_) => return,
            };
            for entry in entries.flatten() {
                let path = entry.path();
                let file_type = match entry.file_type() {
                    Ok(ft) => ft,
                    Err(_) => continue,
                };

                // Skip symlinks to avoid duplicate traversal through linked trees.
                if file_type.is_symlink() {
                    continue;
                }

                let rel = path.strip_prefix(base).unwrap_or(&path);
                if is_duplicate_lib_subtree(rel) {
                    continue;
                }

                if file_type.is_dir() {
                    let dir_name = path.file_name().unwrap_or_default().to_string_lossy();
                    if !EXCLUDED_DIRS.contains(&dir_name.as_ref()) {
                        walk_dir(&path, base, corpus_name, files);
                    }
                } else if file_type.is_file()
                    && path.extension().is_some_and(|e| e == "res" || e == "resi")
                {
                    let size = std::fs::metadata(&path).map(|m| m.len()).unwrap_or(0);
                    let rel = path.strip_prefix(base).unwrap_or(&path);
                    let name = format!("{}/{}", corpus_name, rel.to_string_lossy());
                    let lines = std::fs::read(&path)
                        .map(|b| b.iter().filter(|&&c| c == b'\n').count() as u64)
                        .unwrap_or(0);
                    files.push(TestFile {
                        name,
                        path,
                        size,
                        lines,
                    });
                }
            }
        }

        for (corpus_name, base) in benchmark_corpora() {
            if base.is_dir() {
                walk_dir(&base, &base, &corpus_name, &mut files);
            }
        }

        // Sort by size descending (largest files first)
        files.sort_by(|a, b| b.size.cmp(&a.size));
        files
    }

    /// Parse all discovered files once in-process.
    /// Returns (parsed_file_count, elapsed_duration).
    fn parse_corpus_once(files: &[TestFile]) -> (u64, Duration) {
        let start = Instant::now();
        let mut parsed = 0u64;

        for file in files {
            let bytes = match std::fs::read(&file.path) {
                Ok(b) => b,
                Err(_) => continue,
            };
            let source = crate::source_text::latin1_bytes_to_string(bytes);
            let filename = file.path.to_string_lossy().to_string();
            let is_interface = file
                .path
                .extension()
                .and_then(|s| s.to_str())
                .is_some_and(|ext| ext == "resi" || ext == "mli");

            let mut parser = crate::parser::Parser::new(&filename, &source);
            if is_interface {
                let _ = crate::parser::module::parse_signature(&mut parser);
            } else {
                let _ = crate::parser::module::parse_structure(&mut parser);
            }
            parsed += 1;
        }

        (parsed, start.elapsed())
    }

    fn env_u32(var: &str, default: u32) -> u32 {
        std::env::var(var)
            .ok()
            .and_then(|v| v.parse::<u32>().ok())
            .unwrap_or(default)
    }

    fn percentile_nearest_rank(values: &[f64], percentile: f64) -> f64 {
        let mut sorted = values.to_vec();
        sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let rank = ((percentile / 100.0) * sorted.len() as f64).ceil() as usize;
        let index = rank.saturating_sub(1).min(sorted.len().saturating_sub(1));
        sorted[index]
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
    // In-process benchmark helpers
    // ========================================================================

    /// Benchmark in-process parsing of a single file.
    /// Each iteration includes file I/O + Latin-1 conversion + parsing.
    /// Returns minimum duration over N iterations.
    fn benchmark_in_process_n(source_file: &Path, iterations: u32) -> Option<Duration> {
        let filename = source_file.to_string_lossy().to_string();
        let is_interface = source_file
            .extension()
            .and_then(|s| s.to_str())
            .is_some_and(|ext| ext == "resi" || ext == "mli");

        // Helper: read file, convert to Latin-1 string, parse
        let parse_once = |filename: &str| -> Option<()> {
            let bytes = std::fs::read(source_file).ok()?;
            let source = crate::source_text::latin1_bytes_to_string(bytes);
            let mut parser = crate::parser::Parser::new(filename, &source);
            if is_interface {
                let _ = crate::parser::module::parse_signature(&mut parser);
            } else {
                let _ = crate::parser::module::parse_structure(&mut parser);
            }
            Some(())
        };

        // Warm up (2 runs — primes OS page cache and CPU caches)
        parse_once(&filename)?;
        parse_once(&filename)?;

        // Benchmark: take minimum time (includes file I/O, conversion, and parsing)
        let mut min = Duration::MAX;
        for _ in 0..iterations {
            let start = Instant::now();
            parse_once(&filename)?;
            min = min.min(start.elapsed());
        }

        Some(min)
    }

    // ========================================================================
    // Comprehensive subprocess benchmark: all .res files (700+), 10 iterations each
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
        println!("\nDiscovered {} .res files\n", total);

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

        for (i, file) in files.iter().enumerate() {
            // Progress indicator every 50 files
            if i > 0 && i % 50 == 0 {
                eprintln!("  [{}/{}] ...", i, total);
            }

            match benchmark_file_n(&file.path, ITERATIONS_ALL) {
                Some((rust_min, ocaml_min)) => {
                    let rust_us = rust_min.as_nanos() as f64 / 1000.0;
                    let ocaml_us = ocaml_min.as_nanos() as f64 / 1000.0;
                    let factor = rust_us / ocaml_us;

                    print_result(&file.name, file.size, rust_us, ocaml_us, factor);

                    let r = Result {
                        name: file.name.clone(),
                        size: file.size,
                        factor,
                    };
                    if factor > MAX_SLOWDOWN_FACTOR {
                        failures.push(Result {
                            name: file.name.clone(),
                            size: file.size,
                            factor,
                        });
                    }
                    results.push(r);
                }
                None => {
                    println!(
                        "  {:<70} {:>8} {:>10} {:>10} {:>7}  SKIP",
                        file.name, file.size, "-", "-", "-"
                    );
                    errors.push(file.name.clone());
                }
            }
        }

        println!("{:-<110}", "");
        println!();

        // Aggregate statistics
        let passing = results
            .iter()
            .filter(|r| r.factor <= MAX_SLOWDOWN_FACTOR)
            .count();
        let faster = results.iter().filter(|r| r.factor < 1.0).count();
        let benchmarked = results.len();

        // Stats by size tier
        let tiers: &[(&str, u64, u64)] = &[
            ("Large (>30KB)", 30_000, u64::MAX),
            ("Medium (10-30KB)", 10_000, 30_000),
            ("Small (1-10KB)", 1_000, 10_000),
            ("Tiny (<1KB)", 0, 1_000),
        ];

        println!(
            "  {:<25} {:>6} {:>8} {:>8} {:>10} {:>10} {:>10}",
            "Size Tier", "Files", "Faster", "OK", "Avg Factor", "Min Factor", "Max Factor"
        );
        println!("  {:-<85}", "");

        for &(tier_name, min_size, max_size) in tiers {
            let tier_results: Vec<&Result> = results
                .iter()
                .filter(|r| r.size >= min_size && r.size < max_size)
                .collect();
            if tier_results.is_empty() {
                continue;
            }
            let tier_count = tier_results.len();
            let tier_faster = tier_results.iter().filter(|r| r.factor < 1.0).count();
            let tier_ok = tier_results
                .iter()
                .filter(|r| r.factor >= 1.0 && r.factor <= MAX_SLOWDOWN_FACTOR)
                .count();
            let avg_factor: f64 =
                tier_results.iter().map(|r| r.factor).sum::<f64>() / tier_count as f64;
            let min_factor = tier_results
                .iter()
                .map(|r| r.factor)
                .fold(f64::MAX, f64::min);
            let max_factor = tier_results
                .iter()
                .map(|r| r.factor)
                .fold(f64::MIN, f64::max);

            println!(
                "  {:<25} {:>6} {:>8} {:>8} {:>10.2}x {:>10.2}x {:>10.2}x",
                tier_name, tier_count, tier_faster, tier_ok, avg_factor, min_factor, max_factor
            );
        }

        println!("  {:-<85}", "");
        println!();

        println!(
            "  Overall: {}/{} passing ({} faster, {} within tolerance), {} skipped",
            passing,
            benchmarked,
            faster,
            passing - faster,
            errors.len()
        );

        if !failures.is_empty() {
            println!("\n  Failures ({}):", failures.len());
            // Sort failures by factor descending (worst first)
            let mut sorted_failures = failures;
            sorted_failures.sort_by(|a, b| b.factor.partial_cmp(&a.factor).unwrap());
            for r in &sorted_failures {
                println!("    {:<70} {:>8} {:>7.2}x", r.name, r.size, r.factor);
            }
            panic!(
                "{} benchmark(s) failed - Rust bsc is too slow (max allowed: {:.2}x)",
                sorted_failures.len(),
                MAX_SLOWDOWN_FACTOR
            );
        }
    }

    // ========================================================================
    // In-process benchmark: all files, Rust parser called directly (no subprocess)
    // Run with: cargo test --release --lib -- benchmark_all_inprocess --ignored --nocapture
    // ========================================================================

    #[test]
    #[ignore]
    fn benchmark_all_inprocess() {
        if cfg!(debug_assertions) {
            eprintln!("Skipping benchmark: must run in --release mode");
            return;
        }

        let files = discover_test_files();
        let total = files.len();

        // Check if OCaml binary is available for comparison factors
        let has_ocaml = Path::new(OCAML_BSC).exists();
        let ocaml_iterations: u32 = 5; // fewer iterations since subprocess is slow

        println!("\n=== In-Process Parser Benchmark (no subprocess overhead) ===");
        println!(
            "Discovered {} files, {} iterations each",
            total, ITERATIONS_ALL_INPROCESS
        );
        if has_ocaml {
            println!("OCaml bsc found — showing factor (Rust in-process / OCaml subprocess)");
            println!(
                "Note: factor includes OCaml's subprocess overhead, so true speedup is even better"
            );
        } else {
            println!("OCaml bsc not found — showing absolute performance only");
        }
        println!();

        if has_ocaml {
            println!("{:-<120}", "");
            println!(
                "  {:<60} {:>6} {:>10} {:>10} {:>8} {:>8}  ",
                "File", "Size", "Rust parse", "OCaml subp", "MB/s", "Factor"
            );
            println!("{:-<120}", "");
        } else {
            println!("{:-<90}", "");
            println!(
                "  {:<60} {:>6} {:>10} {:>8}",
                "File", "Size", "Rust parse", "MB/s"
            );
            println!("{:-<90}", "");
        }

        struct InProcResult {
            size: u64,
            lines: u64,
            parse_us: f64,
            throughput: f64,
            factor: Option<f64>,
        }

        let mut results: Vec<InProcResult> = Vec::new();
        let mut skipped: u32 = 0;

        // Temp dir for OCaml subprocess output
        let tmp_dir = if has_ocaml {
            tempfile::tempdir().ok()
        } else {
            None
        };

        for (i, file) in files.iter().enumerate() {
            if i > 0 && i % 100 == 0 {
                eprintln!("  [{}/{}] ...", i, total);
            }

            // In-process Rust parse benchmark
            let parse_time = match benchmark_in_process_n(&file.path, ITERATIONS_ALL_INPROCESS) {
                Some(d) => d,
                None => {
                    skipped += 1;
                    continue;
                }
            };

            let parse_us = parse_time.as_nanos() as f64 / 1000.0;
            let throughput = if file.size > 0 && parse_time.as_nanos() > 0 {
                (file.size as f64) / (parse_time.as_secs_f64() * 1_000_000.0)
            } else {
                0.0
            };

            // Optional OCaml subprocess comparison
            let factor = if has_ocaml {
                if let Some(ref tmp) = tmp_dir {
                    let ocaml_out = tmp.path().join("ocaml.ast");
                    // Warm up
                    run_bsc(OCAML_BSC, &file.path, &ocaml_out);
                    run_bsc(OCAML_BSC, &file.path, &ocaml_out);
                    // Benchmark
                    let mut ocaml_min = Duration::MAX;
                    for _ in 0..ocaml_iterations {
                        if let Some(t) = run_bsc(OCAML_BSC, &file.path, &ocaml_out) {
                            ocaml_min = ocaml_min.min(t);
                        }
                    }
                    if ocaml_min < Duration::MAX {
                        let ocaml_us = ocaml_min.as_nanos() as f64 / 1000.0;
                        let f = parse_us / ocaml_us;
                        let status = if f <= 0.1 {
                            "FAST"
                        } else if f <= 0.5 {
                            "FASTER"
                        } else if f <= 1.0 {
                            "faster"
                        } else {
                            "SLOW"
                        };
                        println!(
                            "  {:<60} {:>6} {:>8.0}us {:>8.0}us {:>8.1} {:>7.2}x  {}",
                            file.name, file.size, parse_us, ocaml_us, throughput, f, status
                        );
                        Some(f)
                    } else {
                        println!(
                            "  {:<60} {:>6} {:>8.0}us {:>8} {:>8.1}",
                            file.name, file.size, parse_us, "err", throughput
                        );
                        None
                    }
                } else {
                    None
                }
            } else {
                println!(
                    "  {:<60} {:>6} {:>8.0}us {:>8.1}",
                    file.name, file.size, parse_us, throughput
                );
                None
            };

            results.push(InProcResult {
                size: file.size,
                lines: file.lines,
                parse_us,
                throughput,
                factor,
            });
        }

        let line_width = if has_ocaml { 120 } else { 90 };
        println!("{:-<width$}", "", width = line_width);
        println!();

        // Size tier summary
        let tiers: &[(&str, u64, u64)] = &[
            ("Large (>30KB)", 30_000, u64::MAX),
            ("Medium (10-30KB)", 10_000, 30_000),
            ("Small (1-10KB)", 1_000, 10_000),
            ("Tiny (<1KB)", 0, 1_000),
        ];

        if has_ocaml {
            println!(
                "  {:<25} {:>6} {:>12} {:>12} {:>12} {:>10} {:>12}",
                "Size Tier",
                "Files",
                "Avg Parse",
                "Min Parse",
                "Max Parse",
                "Avg MB/s",
                "Avg Factor"
            );
        } else {
            println!(
                "  {:<25} {:>6} {:>12} {:>12} {:>12} {:>10}",
                "Size Tier", "Files", "Avg Parse", "Min Parse", "Max Parse", "Avg MB/s"
            );
        }
        println!("  {:-<95}", "");

        for &(tier_name, min_size, max_size) in tiers {
            let tier: Vec<&InProcResult> = results
                .iter()
                .filter(|r| r.size >= min_size && r.size < max_size)
                .collect();
            if tier.is_empty() {
                continue;
            }
            let count = tier.len();
            let avg_us = tier.iter().map(|r| r.parse_us).sum::<f64>() / count as f64;
            let min_us = tier.iter().map(|r| r.parse_us).fold(f64::MAX, f64::min);
            let max_us = tier.iter().map(|r| r.parse_us).fold(f64::MIN, f64::max);
            let avg_throughput = tier.iter().map(|r| r.throughput).sum::<f64>() / count as f64;

            if has_ocaml {
                let factors: Vec<f64> = tier.iter().filter_map(|r| r.factor).collect();
                let avg_factor = if !factors.is_empty() {
                    factors.iter().sum::<f64>() / factors.len() as f64
                } else {
                    0.0
                };
                println!(
                    "  {:<25} {:>6} {:>10.0}us {:>10.0}us {:>10.0}us {:>8.1} {:>10.2}x",
                    tier_name, count, avg_us, min_us, max_us, avg_throughput, avg_factor
                );
            } else {
                println!(
                    "  {:<25} {:>6} {:>10.0}us {:>10.0}us {:>10.0}us {:>8.1}",
                    tier_name, count, avg_us, min_us, max_us, avg_throughput
                );
            }
        }

        println!("  {:-<95}", "");
        println!();

        // Overall statistics
        let total_size: u64 = results.iter().map(|r| r.size).sum();
        let total_lines: u64 = results.iter().map(|r| r.lines).sum();
        let total_time_us: f64 = results.iter().map(|r| r.parse_us).sum();
        let total_time_s = total_time_us / 1_000_000.0;
        let overall_throughput_mbs = if total_time_s > 0.0 {
            (total_size as f64) / total_time_s / 1_000_000.0
        } else {
            0.0
        };
        let overall_loc_per_s = if total_time_s > 0.0 {
            total_lines as f64 / total_time_s
        } else {
            0.0
        };

        println!("  {} files parsed, {} skipped", results.len(), skipped);
        println!(
            "  Total: {:.1} KB, {} lines of code",
            total_size as f64 / 1024.0,
            total_lines
        );
        println!(
            "  Total parse time: {:.1} ms (sum of per-file minimums)",
            total_time_us / 1000.0
        );
        println!(
            "  Throughput: {:.1} MB/s, {:.0} LOC/s ({:.0}K LOC/s)",
            overall_throughput_mbs,
            overall_loc_per_s,
            overall_loc_per_s / 1000.0
        );

        if has_ocaml {
            let factors: Vec<f64> = results.iter().filter_map(|r| r.factor).collect();
            if !factors.is_empty() {
                let avg_factor = factors.iter().sum::<f64>() / factors.len() as f64;
                let min_factor = factors.iter().copied().fold(f64::MAX, f64::min);
                let max_factor = factors.iter().copied().fold(f64::MIN, f64::max);
                println!();
                println!(
                    "  Factor (Rust in-process / OCaml subprocess): avg {:.2}x, min {:.2}x, max {:.2}x",
                    avg_factor, min_factor, max_factor
                );
            }
        }
    }

    // ========================================================================
    // Cold-start benchmark: parse each file once, no warmup
    // Run with: cargo test --release --lib -- benchmark_cold --ignored --nocapture
    // ========================================================================

    #[test]
    #[ignore]
    fn benchmark_cold() {
        if cfg!(debug_assertions) {
            eprintln!("Skipping benchmark: must run in --release mode");
            return;
        }

        let files = discover_test_files();
        let total_lines: u64 = files.iter().map(|f| f.lines).sum();
        let total_size: u64 = files.iter().map(|f| f.size).sum();

        println!("\n=== Cold-Start Benchmark (no warmup, single pass) ===");
        println!(
            "{} files, {} lines, {:.1} KB\n",
            files.len(),
            total_lines,
            total_size as f64 / 1024.0
        );

        let (parsed, elapsed) = parse_corpus_once(&files);
        let elapsed_s = elapsed.as_secs_f64();
        let loc_per_s = total_lines as f64 / elapsed_s;
        let mbs = (total_size as f64) / elapsed_s / 1_000_000.0;

        println!("  {} files parsed in {:.1} ms", parsed, elapsed_s * 1000.0);
        println!(
            "  Throughput: {:.1} MB/s, {:.0}K LOC/s",
            mbs,
            loc_per_s / 1000.0
        );
    }

    // ========================================================================
    // Repeated in-process cold benchmark: parse full corpus in one process
    // Run with:
    //   RAYON_NUM_THREADS=1 PARSER_BENCH_WARMUP=2 PARSER_BENCH_RUNS=10 \
    //   cargo test --release --lib -- benchmark_cold_repeat --ignored --nocapture
    // ========================================================================

    #[test]
    #[ignore]
    fn benchmark_cold_repeat() {
        if cfg!(debug_assertions) {
            eprintln!("Skipping benchmark: must run in --release mode");
            return;
        }

        let warmup_runs = env_u32("PARSER_BENCH_WARMUP", 2);
        let bench_runs = env_u32("PARSER_BENCH_RUNS", 10);
        if bench_runs == 0 {
            eprintln!("PARSER_BENCH_RUNS must be > 0");
            return;
        }

        let files = discover_test_files();
        let total_lines: u64 = files.iter().map(|f| f.lines).sum();
        let total_size: u64 = files.iter().map(|f| f.size).sum();

        println!("\n=== In-Process Repeated Parser Benchmark ===");
        println!(
            "{} files, {} lines, {:.1} KB",
            files.len(),
            total_lines,
            total_size as f64 / 1024.0
        );
        println!(
            "Warmup runs: {}, measured runs: {}\n",
            warmup_runs, bench_runs
        );

        for i in 0..warmup_runs {
            let (_parsed, elapsed) = parse_corpus_once(&files);
            println!(
                "Warmup {:>2}/{:>2}: {:>7.1} ms",
                i + 1,
                warmup_runs,
                elapsed.as_secs_f64() * 1000.0
            );
        }

        if warmup_runs > 0 {
            println!();
        }

        let mut elapsed_ms_values: Vec<f64> = Vec::with_capacity(bench_runs as usize);
        let mut kloc_per_s_values: Vec<f64> = Vec::with_capacity(bench_runs as usize);
        let mut mb_per_s_values: Vec<f64> = Vec::with_capacity(bench_runs as usize);

        for i in 0..bench_runs {
            let (parsed, elapsed) = parse_corpus_once(&files);
            let elapsed_s = elapsed.as_secs_f64();
            let elapsed_ms = elapsed_s * 1000.0;
            let kloc_per_s = total_lines as f64 / elapsed_s / 1000.0;
            let mb_per_s = total_size as f64 / elapsed_s / 1_000_000.0;

            elapsed_ms_values.push(elapsed_ms);
            kloc_per_s_values.push(kloc_per_s);
            mb_per_s_values.push(mb_per_s);

            println!(
                "Run {:>2}/{:>2}: {:>7.1} ms {:>8.1} KLOC/s {:>6.2} MB/s ({} files)",
                i + 1,
                bench_runs,
                elapsed_ms,
                kloc_per_s,
                mb_per_s,
                parsed
            );
        }

        let min_kloc = kloc_per_s_values
            .iter()
            .copied()
            .fold(f64::INFINITY, f64::min);
        let max_kloc = kloc_per_s_values
            .iter()
            .copied()
            .fold(f64::NEG_INFINITY, f64::max);
        let median_kloc = percentile_nearest_rank(&kloc_per_s_values, 50.0);
        let p95_kloc = percentile_nearest_rank(&kloc_per_s_values, 95.0);

        let min_ms = elapsed_ms_values
            .iter()
            .copied()
            .fold(f64::INFINITY, f64::min);
        let max_ms = elapsed_ms_values
            .iter()
            .copied()
            .fold(f64::NEG_INFINITY, f64::max);
        let median_ms = percentile_nearest_rank(&elapsed_ms_values, 50.0);
        let p95_ms = percentile_nearest_rank(&elapsed_ms_values, 95.0);

        let min_mbs = mb_per_s_values
            .iter()
            .copied()
            .fold(f64::INFINITY, f64::min);
        let median_mbs = percentile_nearest_rank(&mb_per_s_values, 50.0);

        println!("\nSummary");
        println!("=======");
        println!(
            "Corpus: {} files, {} LOC, {:.1} KB",
            files.len(),
            total_lines,
            total_size as f64 / 1024.0
        );
        println!(
            "KLOC/s: min {:.1}  median {:.1}  p95 {:.1}  max {:.1}",
            min_kloc, median_kloc, p95_kloc, max_kloc
        );
        println!(
            "ms:     min {:.1}  median {:.1}  p95 {:.1}  max {:.1}",
            min_ms, median_ms, p95_ms, max_ms
        );
        println!("MB/s:   min {:.2}  median {:.2}", min_mbs, median_mbs);
        println!(
            "Best-case throughput (max KLOC/s / min ms): {:.1} KLOC/s @ {:.1} ms",
            max_kloc, min_ms
        );
    }

    // ========================================================================
    // Cold round-trip benchmark: read → parse → print → write, single pass
    // Run with: cargo test --release --lib -- benchmark_roundtrip_cold --ignored --nocapture
    // ========================================================================

    #[test]
    #[ignore]
    fn benchmark_roundtrip_cold() {
        if cfg!(debug_assertions) {
            eprintln!("Skipping benchmark: must run in --release mode");
            return;
        }

        let files = discover_test_files();
        let total_lines: u64 = files.iter().map(|f| f.lines).sum();
        let total_size: u64 = files.iter().map(|f| f.size).sum();

        let tmp_dir = tempfile::tempdir().expect("failed to create temp dir");
        let out_path = tmp_dir.path().join("output.res");

        println!("\n=== Cold Round-Trip Benchmark: read → parse → print → write ===");
        println!(
            "{} files, {} lines, {:.1} KB\n",
            files.len(),
            total_lines,
            total_size as f64 / 1024.0
        );

        let start = Instant::now();
        let mut processed = 0u64;
        for file in &files {
            // 1. READ
            let bytes = match std::fs::read(&file.path) {
                Ok(b) => b,
                Err(_) => continue,
            };
            let source = crate::source_text::latin1_bytes_to_string(bytes);
            let filename = file.path.to_string_lossy().to_string();
            let is_interface = file
                .path
                .extension()
                .and_then(|s| s.to_str())
                .is_some_and(|ext| ext == "resi" || ext == "mli");

            // 2. PARSE
            let mut parser = crate::parser::Parser::new(&filename, &source);
            let printed = if is_interface {
                let sig = crate::parser::module::parse_signature(&mut parser);
                let comments = parser.take_comments();
                // 3. PRINT
                crate::parser::printer::print_interface(
                    &sig,
                    comments,
                    crate::parser::printer::DEFAULT_PRINT_WIDTH,
                    parser.arena_mut(),
                )
            } else {
                let structure = crate::parser::module::parse_structure(&mut parser);
                let comments = parser.take_comments();
                // 3. PRINT
                crate::parser::printer::print_implementation(
                    &structure,
                    comments,
                    crate::parser::printer::DEFAULT_PRINT_WIDTH,
                    parser.arena_mut(),
                )
            };

            // 4. WRITE
            let _ = std::fs::write(&out_path, printed.as_bytes());
            processed += 1;
        }
        let elapsed = start.elapsed();
        let elapsed_s = elapsed.as_secs_f64();
        let loc_per_s = total_lines as f64 / elapsed_s;
        let mbs = (total_size as f64) / elapsed_s / 1_000_000.0;

        println!(
            "  {} files processed in {:.1} ms",
            processed,
            elapsed_s * 1000.0
        );
        println!(
            "  Throughput: {:.1} MB/s, {:.0}K LOC/s",
            mbs,
            loc_per_s / 1000.0
        );
    }

    // ========================================================================
    // Parallel cold-start benchmark: parse all files with rayon, no warmup
    // Run with: cargo test --release --lib -- benchmark_parallel_cold --ignored --nocapture
    // ========================================================================

    #[test]
    #[ignore]
    fn benchmark_parallel_cold() {
        use rayon::prelude::*;
        use std::sync::atomic::{AtomicU64, Ordering};

        if cfg!(debug_assertions) {
            eprintln!("Skipping benchmark: must run in --release mode");
            return;
        }

        let files = discover_test_files();
        let total_lines: u64 = files.iter().map(|f| f.lines).sum();
        let total_size: u64 = files.iter().map(|f| f.size).sum();
        let num_threads = rayon::current_num_threads();

        println!(
            "\n=== Parallel Cold-Start Parse Benchmark ({} threads) ===",
            num_threads
        );
        println!(
            "{} files, {} lines, {:.1} KB\n",
            files.len(),
            total_lines,
            total_size as f64 / 1024.0
        );

        let parsed = AtomicU64::new(0);

        let start = Instant::now();
        files.par_iter().for_each(|file| {
            let bytes = match std::fs::read(&file.path) {
                Ok(b) => b,
                Err(_) => return,
            };
            let source = crate::source_text::latin1_bytes_to_string(bytes);
            let filename = file.path.to_string_lossy().to_string();
            let is_interface = file
                .path
                .extension()
                .and_then(|s| s.to_str())
                .is_some_and(|ext| ext == "resi" || ext == "mli");

            let mut parser = crate::parser::Parser::new(&filename, &source);
            if is_interface {
                let _ = crate::parser::module::parse_signature(&mut parser);
            } else {
                let _ = crate::parser::module::parse_structure(&mut parser);
            }
            parsed.fetch_add(1, Ordering::Relaxed);
        });
        let elapsed = start.elapsed();
        let elapsed_s = elapsed.as_secs_f64();
        let loc_per_s = total_lines as f64 / elapsed_s;
        let mbs = (total_size as f64) / elapsed_s / 1_000_000.0;
        let parsed_count = parsed.load(Ordering::Relaxed);

        println!(
            "  {} files parsed in {:.1} ms ({} threads)",
            parsed_count,
            elapsed_s * 1000.0,
            num_threads
        );
        println!(
            "  Throughput: {:.1} MB/s, {:.0}K LOC/s",
            mbs,
            loc_per_s / 1000.0
        );
        println!(
            "  Per-thread: {:.1} MB/s, {:.0}K LOC/s",
            mbs / num_threads as f64,
            loc_per_s / 1000.0 / num_threads as f64
        );
    }

    // ========================================================================
    // Parallel comparison: OCaml subprocess vs Rust subprocess vs Rust in-process
    // Run with: cargo test --release --lib -- benchmark_parallel_compare --ignored --nocapture
    // ========================================================================

    #[test]
    #[ignore]
    fn benchmark_parallel_compare() {
        use rayon::prelude::*;
        use std::sync::atomic::{AtomicU64, Ordering};

        if cfg!(debug_assertions) {
            eprintln!("Skipping benchmark: must run in --release mode");
            return;
        }

        let has_rust_bsc = Path::new(RUST_BSC).exists();
        let has_ocaml_bsc = Path::new(OCAML_BSC).exists();
        if !has_rust_bsc || !has_ocaml_bsc {
            eprintln!(
                "Skipping: need both bsc binaries\n  Rust:  {} ({})\n  OCaml: {} ({})",
                RUST_BSC,
                if has_rust_bsc { "found" } else { "missing" },
                OCAML_BSC,
                if has_ocaml_bsc { "found" } else { "missing" },
            );
            return;
        }

        let files = discover_test_files();
        let total_lines: u64 = files.iter().map(|f| f.lines).sum();
        let total_size: u64 = files.iter().map(|f| f.size).sum();
        let num_threads = rayon::current_num_threads();

        println!("\n=== Parallel Comparison: OCaml subp vs Rust subp vs Rust in-process ===");
        println!(
            "{} files, {} lines, {:.1} KB, {} threads\n",
            files.len(),
            total_lines,
            total_size as f64 / 1024.0,
            num_threads
        );

        // --- OCaml subprocess parallel ---
        {
            let count = AtomicU64::new(0);
            let start = Instant::now();
            files.par_iter().for_each(|file| {
                let tmp = tempfile::NamedTempFile::new().unwrap();
                let result = Command::new(OCAML_BSC)
                    .arg("-bs-ast")
                    .arg("-o")
                    .arg(tmp.path())
                    .arg(&file.path)
                    .output();
                if result.is_ok_and(|o| o.status.success()) {
                    count.fetch_add(1, Ordering::Relaxed);
                }
            });
            let elapsed = start.elapsed();
            let elapsed_s = elapsed.as_secs_f64();
            let kloc = total_lines as f64 / elapsed_s / 1000.0;
            let mbs = (total_size as f64) / elapsed_s / 1_000_000.0;
            println!(
                "  OCaml bsc (subprocess):     {:>7.1} ms  {:>6.1} MB/s  {:>7.0}K LOC/s  ({} files)",
                elapsed_s * 1000.0,
                mbs,
                kloc,
                count.load(Ordering::Relaxed)
            );
        }

        // --- Rust subprocess parallel ---
        {
            let count = AtomicU64::new(0);
            let start = Instant::now();
            files.par_iter().for_each(|file| {
                let tmp = tempfile::NamedTempFile::new().unwrap();
                let result = Command::new(RUST_BSC)
                    .arg("-bs-ast")
                    .arg("-o")
                    .arg(tmp.path())
                    .arg(&file.path)
                    .output();
                if result.is_ok_and(|o| o.status.success()) {
                    count.fetch_add(1, Ordering::Relaxed);
                }
            });
            let elapsed = start.elapsed();
            let elapsed_s = elapsed.as_secs_f64();
            let kloc = total_lines as f64 / elapsed_s / 1000.0;
            let mbs = (total_size as f64) / elapsed_s / 1_000_000.0;
            println!(
                "  Rust bsc (subprocess):      {:>7.1} ms  {:>6.1} MB/s  {:>7.0}K LOC/s  ({} files)",
                elapsed_s * 1000.0,
                mbs,
                kloc,
                count.load(Ordering::Relaxed)
            );
        }

        // --- Rust in-process parallel ---
        {
            let count = AtomicU64::new(0);
            let start = Instant::now();
            files.par_iter().for_each(|file| {
                let bytes = match std::fs::read(&file.path) {
                    Ok(b) => b,
                    Err(_) => return,
                };
                let source = crate::source_text::latin1_bytes_to_string(bytes);
                let filename = file.path.to_string_lossy().to_string();
                let is_interface = file
                    .path
                    .extension()
                    .and_then(|s| s.to_str())
                    .is_some_and(|ext| ext == "resi" || ext == "mli");

                let mut parser = crate::parser::Parser::new(&filename, &source);
                if is_interface {
                    let _ = crate::parser::module::parse_signature(&mut parser);
                } else {
                    let _ = crate::parser::module::parse_structure(&mut parser);
                }
                count.fetch_add(1, Ordering::Relaxed);
            });
            let elapsed = start.elapsed();
            let elapsed_s = elapsed.as_secs_f64();
            let kloc = total_lines as f64 / elapsed_s / 1000.0;
            let mbs = (total_size as f64) / elapsed_s / 1_000_000.0;
            println!(
                "  Rust in-process (parallel):  {:>7.1} ms  {:>6.1} MB/s  {:>7.0}K LOC/s  ({} files)",
                elapsed_s * 1000.0,
                mbs,
                kloc,
                count.load(Ordering::Relaxed)
            );
        }
    }
}
