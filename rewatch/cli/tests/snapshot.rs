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
fn one_belt_array_reference_decodes_one_belt_and_two_runtime_modules() {
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
        .env_remove("RESCRIPT_FULL_BUILD").env("RESCRIPT_SNAPSHOT", "require")
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
    // Belt_Array plus the implicit runtime opens (Stdlib and Pervasives).
    // Runtime modules now participate in the same decode counter as Belt.
    assert!(stderr.contains("snapshot_modules_decoded=3\n"), "{stderr}");
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
        .env_remove("RESCRIPT_COMPILER_COUNTERS").env_remove("RESCRIPT_FULL_BUILD").env("RESCRIPT_SNAPSHOT", "require")
        .stdout(Stdio::piped()).stderr(Stdio::piped());
    command.env("RESCRIPT_SNAPSHOT", if full { "off" } else { "require" });
    let mut child = command.spawn().unwrap();
    let deadline = Instant::now() + Duration::from_secs(10);
    while child.try_wait().unwrap().is_none() {
        if Instant::now() >= deadline { child.kill().unwrap(); panic!("template fixture exceeded ten seconds"); }
        std::thread::sleep(Duration::from_millis(10));
    }
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{}\n{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
}

#[test]
fn snapshot_require_rejects_changed_sources_and_off_reports_its_reason() {
    let checkout = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap();
    let project = tempfile::tempdir().unwrap();
    let belt = project.path().join("node_modules/@rescript/belt");
    copy_sources(&checkout.join("packages/@rescript/belt/src"), &belt.join("src"));
    std::fs::copy(checkout.join("packages/@rescript/belt/rescript.json"), belt.join("rescript.json")).unwrap();
    std::fs::create_dir(project.path().join("src")).unwrap();
    std::fs::write(project.path().join("rescript.json"), r#"{
        "name":"snapshot-switch-test", "sources":["src"], "dependencies":["@rescript/belt"],
        "package-specs":{"module":"esmodule","suffix":".mjs","in-source":true}
    }"#).unwrap();
    std::fs::write(project.path().join("src/Main.res"), "let size = Belt_Array.length([1])\n").unwrap();
    use std::io::Write;
    std::fs::OpenOptions::new().append(true).open(belt.join("src/Belt_Array.res")).unwrap().write_all(b"\n// patched\n").unwrap();
    for (mode, success, reason) in [
        ("require", false, "sources differ"),
        ("off", true, "disabled by RESCRIPT_SNAPSHOT=off"),
    ] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_rescript"))
            .arg("-v").arg("build").arg(project.path())
            .env("RESCRIPT_RUNTIME", checkout.join("packages/@rescript/runtime"))
            .env("RESCRIPT_SNAPSHOT", mode).env_remove("RESCRIPT_FULL_BUILD")
            .stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
        let deadline = Instant::now() + Duration::from_secs(10);
        while child.try_wait().unwrap().is_none() {
            if Instant::now() >= deadline { child.kill().unwrap(); panic!("switch fixture exceeded ten seconds"); }
            std::thread::sleep(Duration::from_millis(10));
        }
        let output = child.wait_with_output().unwrap();
        let text = format!("{}{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.status.success(), success, "{text}");
        assert!(text.contains(reason), "{text}");
    }
}

#[test]
fn relocated_runtime_without_config_honors_require_and_off() {
    let checkout = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap();
    let project = tempfile::tempdir().unwrap();
    let runtime = tempfile::tempdir().unwrap();
    copy_sources(&checkout.join("packages/@rescript/runtime"), runtime.path());
    std::fs::create_dir(project.path().join("src")).unwrap();
    std::fs::write(project.path().join("rescript.json"), r#"{
        "name":"runtime-snapshot-test", "sources":["src"],
        "package-specs":{"module":"esmodule","suffix":".mjs","in-source":true}
    }"#).unwrap();
    for (mode, patch, success) in [("require", false, true), ("require", true, false), ("off", false, true)] {
        if patch {
            use std::io::Write;
            std::fs::OpenOptions::new().append(true).open(runtime.path().join("Pervasives.res"))
                .unwrap().write_all(b"\n// patched runtime\n").unwrap();
        }
        // Force a compilation so the no-change planner cannot skip verification.
        std::fs::write(project.path().join("src/Main.res"), format!("let value = list{{1, 2}}->List.length\n// {mode} {patch}\n")).unwrap();
        let mut child = Command::new(env!("CARGO_BIN_EXE_rescript"))
            .arg("-v").arg("build").arg(project.path())
            .env("RESCRIPT_RUNTIME", runtime.path()).env("RESCRIPT_SNAPSHOT", mode)
            .env_remove("RESCRIPT_FULL_BUILD")
            .stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
        let deadline = Instant::now() + Duration::from_secs(10);
        while child.try_wait().unwrap().is_none() {
            if Instant::now() >= deadline { child.kill().unwrap(); panic!("runtime fixture exceeded ten seconds"); }
            std::thread::sleep(Duration::from_millis(10));
        }
        let output = child.wait_with_output().unwrap();
        let text = format!("{}{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
        assert_eq!(output.status.success(), success, "{text}");
        if patch { assert!(text.contains("Not using the prebuilt @rescript/runtime: its sources differ"), "{text}"); }
        if mode == "off" { assert!(text.contains("Not using the prebuilt @rescript/runtime: disabled by RESCRIPT_SNAPSHOT=off"), "{text}"); }
    }
}

// All developer-command subprocesses have the same tight bound as build tests.
fn snapshot_command(runtime: &Path, args: &[&str]) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_rescript"))
        .args(args).env("RESCRIPT_RUNTIME", runtime)
        .stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
    let deadline = Instant::now() + Duration::from_secs(10);
    while child.try_wait().unwrap().is_none() {
        if Instant::now() >= deadline { child.kill().unwrap(); panic!("snapshot command exceeded ten seconds"); }
        std::thread::sleep(Duration::from_millis(10));
    }
    child.wait_with_output().unwrap()
}

#[test]
fn snapshot_write_is_deterministic_across_processes() {
    let runtime = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../packages/@rescript/runtime").canonicalize().unwrap();
    let output = tempfile::tempdir().unwrap();
    let first = output.path().join("first.bin");
    let second = output.path().join("second.bin");
    for file in [&first, &second] {
        let result = snapshot_command(&runtime, &["snapshot", "--write", file.to_str().unwrap()]);
        assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    }
    assert_eq!(std::fs::read(first).unwrap(), std::fs::read(second).unwrap());
}

#[test]
fn snapshot_check_detects_package_edits_and_added_modules() {
    let checkout = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").canonicalize().unwrap();
    let packages = tempfile::tempdir().unwrap();
    let runtime = packages.path().join("runtime");
    let belt = packages.path().join("belt");
    copy_sources(&checkout.join("packages/@rescript/runtime"), &runtime);
    copy_sources(&checkout.join("packages/@rescript/belt/src"), &belt.join("src"));
    for name in ["runtime", "belt"] {
        std::fs::copy(checkout.join(format!("packages/@rescript/{name}/rescript.json")),
            packages.path().join(name).join("rescript.json")).unwrap();
    }
    let unchanged = snapshot_command(&runtime, &["snapshot", "--check"]);
    assert!(unchanged.status.success(), "{}", String::from_utf8_lossy(&unchanged.stderr));
    for (file, before, after, package, module) in [
        (runtime.join("Stdlib_Int.res"), "2147483647", "2147483646", "@rescript/runtime", "Stdlib_Int"),
        (belt.join("src/Belt_Array.res"), "i >= 0", "i >= 1", "@rescript/belt", "Belt_Array"),
    ] {
        let original = std::fs::read_to_string(&file).unwrap();
        assert!(original.contains(before));
        std::fs::write(&file, original.replacen(before, after, 1)).unwrap();
        let changed = snapshot_command(&runtime, &["snapshot", "--check"]);
        let error = String::from_utf8_lossy(&changed.stderr);
        assert!(!changed.status.success() && error.contains(package) && error.contains(module), "{error}");
        std::fs::write(file, original).unwrap();
    }
    std::fs::write(runtime.join("AddedSnapshotTest.res"), "let value = 1\n").unwrap();
    let added = snapshot_command(&runtime, &["snapshot", "--check"]);
    let error = String::from_utf8_lossy(&added.stderr);
    assert!(!added.status.success() && error.contains("@rescript/runtime") && error.contains("AddedSnapshotTest"), "{error}");
}

#[test]
fn snapshot_command_is_hidden() {
    let help = snapshot_command(Path::new("."), &["--help"]);
    assert!(help.status.success());
    assert!(!String::from_utf8_lossy(&help.stdout).contains("snapshot"));
}
