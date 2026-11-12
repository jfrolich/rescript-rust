#[path = "support/mapping_sequence.rs"]
mod mapping_sequence;
// Source-map sequence oracle. Requires the OCaml reference artifacts used by the existing
// compiler integration tests (build-reference for runtime and tests/tests).
use js_reformat::{ReformatOptions, reformat};
use rescript_compiler::{
    driver::{CompilerOptions, compile_file_to_js_with_options},
    emit::{PrinterMode, PrinterStats},
    js_ir::ModuleFormat,
};
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
    sync::Arc,
};

fn sources(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            sources(&path, out);
        } else if path.extension().is_some_and(|e| e == "res") {
            out.push(path);
        }
    }
}

#[test]
fn in_repository_corpora() {
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(run)
        .unwrap()
        .join()
        .unwrap();
}

fn run() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let runtime = root.join("packages/@rescript/runtime");
    let mut files = Vec::new();
    sources(&root.join("tests/tests/src"), &mut files);
    // Runtime sources are at the package root; lib contains generated copies.
    for entry in std::fs::read_dir(&runtime).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|e| e == "res") {
            files.push(path);
        }
    }
    sources(&root.join("tests/build_tests/source_map/src"), &mut files);
    files.sort();
    let output = tempfile::tempdir().unwrap();
    // Alias-bearing interfaces may need their source fallback. build-reference
    // writes artifacts, not the flat source copies an in-process build leaves.
    let source_dirs: std::collections::BTreeSet<_> = files
        .iter()
        .map(|path| path.parent().unwrap().to_path_buf())
        .collect();
    assert!(
        files.len() > 700,
        "expected full corpora, not a filtered sample"
    );
    let mode = ReformatOptions {
        split_file: true,
        drop_decoration_comments: true,
        ..Default::default()
    };
    let mut supported = 0;
    let mut mapped_outputs = 0;
    let mut fallback = BTreeMap::new();
    let mut failures = Vec::new();
    for path in &files {
        let is_runtime = path.parent() == Some(runtime.as_path());
        // tests/tests publishes only ESM dependency metadata. Runtime publishes
        // both formats; CommonJS core shapes also run in the source unit oracle.
        let formats: &[ModuleFormat] = if is_runtime || path.starts_with(root.join("tests/build_tests/source_map")) {
            &[ModuleFormat::EsModule, ModuleFormat::CommonJs]
        } else {
            &[ModuleFormat::EsModule]
        };
        for &format in formats {
            let module = path.file_stem().unwrap().to_str().unwrap();
            let mut options = CompilerOptions {
                js_printer: PrinterMode::Legacy,
                runtime_path: Some(runtime.clone()),
                include_paths: [
                    root.join("tests/tests/lib/rescript"),
                    root.join("tests/build_tests/source_map/lib/rescript"),
                    root.join("tests/dependencies/rescript-react/lib/rescript"),
                    runtime.join("lib/rescript"),
                ]
                .into_iter()
                .chain(source_dirs.iter().cloned())
                .collect(),
                source_filename: Some(path.to_string_lossy().into_owned()),
                source_map: rescript_compiler::js_ir::source_map::SourceMapMode::Hidden,
                output_path: Some(output.path().join(path.file_name().unwrap()).with_extension(if format == ModuleFormat::EsModule {
                    "mjs"
                } else {
                    "cjs"
                })),
                output_module_format: Some(format),
                module_name: Some(format!(
                    "{}{}",
                    module[..1].to_ascii_uppercase(),
                    &module[1..]
                )),
                warning_specs: vec!["-a".into()],
                make_runtime: is_runtime,
                nopervasives: is_runtime,
                open_modules: if is_runtime {
                    vec!["Pervasives".into()]
                } else {
                    vec![]
                },
                no_version_header: is_runtime,
                experimental_let_unwrap: true,
                check_div_by_zero: !is_runtime,
                ..CompilerOptions::default()
            };
            let legacy = compile_file_to_js_with_options(path, &options)
                .unwrap_or_else(|e| panic!("legacy {}: {e:#}", path.display()));
            let map_path = format!("{}.map", options.output_path.as_ref().unwrap().display());
            let legacy_map = std::fs::read_to_string(&map_path).unwrap();
            let stats = Arc::new(PrinterStats::default());
            options.js_printer = PrinterMode::Oxc(stats.clone());
            let actual = compile_file_to_js_with_options(path, &options)
                .unwrap_or_else(|e| panic!("oxc {}: {e:#}", path.display()));
            let actual_map = std::fs::read_to_string(&map_path).unwrap();
            assert_eq!(mapping_sequence::sequence(&legacy_map), mapping_sequence::sequence(&actual_map), "mapping sequence: {}", path.display());
            let coverage = stats.snapshot();
            assert_eq!(
                coverage.supported + coverage.unsupported.values().sum::<usize>(),
                1
            );
            if coverage.supported == 0 {
                assert_eq!(legacy_map, actual_map, "fallback maps: {}", path.display());
                assert_eq!(
                    actual,
                    legacy,
                    "fallback must be byte-identical: {}",
                    path.display()
                );
                for (reason, count) in coverage.unsupported {
                    let entry = fallback
                        .entry(reason)
                        .or_insert((0, path.strip_prefix(root).unwrap().to_path_buf()));
                    entry.0 += count;
                }
            } else {
                supported += 1;
                mapped_outputs += usize::from(!mapping_sequence::sequence(&actual_map).is_empty());
                let expected = reformat(&legacy, mode)
                    .unwrap_or_else(|e| panic!("reference {}: {e}", path.display()));
                if expected != actual {
                    failures.push(format!("{} {format:?}: reference differs\nEXPECTED:\n{expected}\nACTUAL:\n{actual}", path.strip_prefix(root).unwrap().display()));
                }
                let normalized = reformat(&actual, mode)
                    .unwrap_or_else(|e| panic!("candidate {}: {e}", path.display()));
                if normalized != actual {
                    failures.push(format!(
                        "{} {format:?}: not a fixed point",
                        path.strip_prefix(root).unwrap().display()
                    ));
                }
            }
        }
    }
    println!(
        "OXC SOURCE MAP ORACLE: {} source files; {supported} supported outputs; {} fallbacks; {} differences",
        files.len(),
        fallback.values().map(|(n, _)| n).sum::<usize>(),
        failures.len()
    );
    println!("Supported outputs with nonempty mappings: {mapped_outputs}");
    assert!(mapped_outputs > 0);
    for (reason, (count, example)) in fallback {
        println!("{count}\t{reason}\t{}", example.display());
    }
    assert!(supported > 0, "oracle must exercise the AST emitter");
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

#[test]
fn attachment_modes_keep_metadata_and_nonempty_sequences() {
    use rescript_compiler::js_ir::source_map::{SourceMapMode, inline_comment};
    let temp = tempfile::tempdir().unwrap();
    let source = temp.path().join("Mapped.res");
    let output = temp.path().join("Mapped.mjs");
    std::fs::write(&source, "let text = \"😀\"\nlet identity = x => x\n").unwrap();
    let stats = Arc::new(PrinterStats::default());
    let mut options = CompilerOptions {
        source_filename: Some(source.to_string_lossy().into_owned()),
        output_path: Some(output.clone()),
        source_map: SourceMapMode::Hidden,
        source_map_sources_content: true,
        source_map_root: "rescript://sources/".into(),
        ..CompilerOptions::default()
    };
    compile_file_to_js_with_options(&source, &options).unwrap();
    let map_path = output.with_extension("mjs.map");
    let legacy = std::fs::read_to_string(&map_path).unwrap();
    options.js_printer = PrinterMode::Oxc(stats.clone());
    let hidden = compile_file_to_js_with_options(&source, &options).unwrap();
    let actual = std::fs::read_to_string(&map_path).unwrap();
    assert!(!mapping_sequence::sequence(&actual).is_empty());
    assert_eq!(mapping_sequence::sequence(&legacy), mapping_sequence::sequence(&actual));
    let metadata: serde_json::Value = serde_json::from_str(&actual).unwrap();
    assert_eq!(metadata["sources"], serde_json::json!(["Mapped.res"]));
    assert_eq!(metadata["sourceRoot"], "rescript://sources/");
    assert_eq!(metadata["sourcesContent"][0], std::fs::read_to_string(&source).unwrap());
    assert_eq!(metadata["names"], serde_json::json!([]));
    options.source_map = SourceMapMode::Linked;
    let linked = compile_file_to_js_with_options(&source, &options).unwrap();
    assert_eq!(linked, format!("{hidden}//# sourceMappingURL=Mapped.mjs.map\n"));
    assert_eq!(std::fs::read_to_string(&map_path).unwrap(), actual);
    options.source_map = SourceMapMode::Inline;
    let inline = compile_file_to_js_with_options(&source, &options).unwrap();
    assert_eq!(inline, format!("{hidden}{}", inline_comment(&actual)));
    assert!(!map_path.exists());
    assert_eq!(stats.snapshot().supported, 3);
}
