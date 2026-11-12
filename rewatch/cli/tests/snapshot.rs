//! The snapshot must leave unreferenced Belt cores in the executable.
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

fn copy_sources(source: &Path, target: &Path) {
    std::fs::create_dir_all(target).unwrap();
    for entry in std::fs::read_dir(source).unwrap() {
        let entry = entry.unwrap();
        if entry.path().extension().is_some_and(|ext| ext == "res" || ext == "resi") {
            std::fs::copy(entry.path(), target.join(entry.file_name())).unwrap();
        }
    }
}

#[test]
fn one_belt_array_reference_decodes_one_snapshot_module() {
    let checkout = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap();
    let project = tempfile::tempdir().unwrap();
    let belt = project.path().join("node_modules/@rescript/belt");
    copy_sources(&checkout.join("packages/@rescript/belt/src"), &belt.join("src"));
    std::fs::copy(checkout.join("packages/@rescript/belt/rescript.json"), belt.join("rescript.json")).unwrap();
    std::fs::create_dir(project.path().join("src")).unwrap();
    std::fs::write(project.path().join("rescript.json"), r#"{
        "name":"snapshot-lazy-test", "sources":["src"], "dependencies":["@rescript/belt"],
        "package-specs":{"module":"esmodule","suffix":".mjs","in-source":true}
    }"#).unwrap();
    std::fs::write(project.path().join("src/Main.res"), "let size = Belt_Array.length([1, 2, 3])\n").unwrap();
    let mut child = Command::new(env!("CARGO_BIN_EXE_rescript"))
        .arg("build").arg(project.path())
        .env("RESCRIPT_RUNTIME", checkout.join("packages/@rescript/runtime"))
        .env("RESCRIPT_COMPILER_COUNTERS", "1")
        .env_remove("RESCRIPT_FULL_BUILD")
        .stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
    let deadline = Instant::now() + Duration::from_secs(10);
    while child.try_wait().unwrap().is_none() {
        if Instant::now() >= deadline {
            child.kill().unwrap();
            panic!("snapshot fixture exceeded ten seconds");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
    let output = child.wait_with_output().unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert!(stdout.contains("Compiled 1 module"), "{stdout}");
    assert!(stderr.contains("snapshot_modules_decoded=1\n"), "{stderr}");
}

#[test]
fn belt_templates_match_source_for_formats_layouts_and_suffixes() {
    let checkout = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap();
    let project = tempfile::tempdir().unwrap();
    let belt = project.path().join("node_modules/@rescript/belt");
    copy_sources(&checkout.join("packages/@rescript/belt/src"), &belt.join("src"));
    std::fs::copy(checkout.join("packages/@rescript/belt/rescript.json"), belt.join("rescript.json")).unwrap();
    std::fs::create_dir(project.path().join("src")).unwrap();
    std::fs::write(project.path().join("src/Main.res"), "let size = Belt_Array.length([1, 2, 3])\n").unwrap();
    for in_source in [false, true] {
        for (esm, cjs) in [(".mjs", ".cjs"), (".res.mjs", ".res.cjs")] {
            std::fs::write(project.path().join("rescript.json"), format!(r#"{{
                "name":"snapshot-template-test", "sources":["src"], "dependencies":["@rescript/belt"],
                "package-specs":[{{"module":"esmodule","suffix":"{esm}","in-source":{in_source}}},
                                 {{"module":"commonjs","suffix":"{cjs}","in-source":{in_source}}}]
            }}"#)).unwrap();
            run_build(project.path(), &checkout, false);
            let mut generated = Vec::new();
            for entry in std::fs::read_dir(belt.join("src")).unwrap() {
                let path = entry.unwrap().path();
                if path.extension().is_none_or(|ext| ext != "res") { continue; }
                let name = path.file_stem().unwrap().to_str().unwrap();
                for (suffix, folder) in [(esm, "es6"), (cjs, "js")] {
                    let output = if in_source { belt.join("src") } else { belt.join("lib").join(folder).join("src") }
                        .join(format!("{name}{suffix}"));
                    generated.push((output.clone(), std::fs::read(output).unwrap()));
                }
            }
            assert_eq!(generated.len(), 86);
            run_build(project.path(), &checkout, true);
            for (path, expected) in generated {
                assert_eq!(std::fs::read(&path).unwrap(), expected, "{}", path.display());
            }
        }
    }
}

fn run_build(project: &Path, checkout: &Path, full: bool) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_rescript"));
    command.arg("build").arg(project)
        .env("RESCRIPT_RUNTIME", checkout.join("packages/@rescript/runtime"))
        .env_remove("RESCRIPT_COMPILER_COUNTERS").env_remove("RESCRIPT_FULL_BUILD")
        .stdout(Stdio::piped()).stderr(Stdio::piped());
    if full { command.env("RESCRIPT_FULL_BUILD", "1"); }
    let mut child = command.spawn().unwrap();
    let deadline = Instant::now() + Duration::from_secs(10);
    while child.try_wait().unwrap().is_none() {
        if Instant::now() >= deadline { child.kill().unwrap(); panic!("template fixture exceeded ten seconds"); }
        std::thread::sleep(Duration::from_millis(10));
    }
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{}\n{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
}
