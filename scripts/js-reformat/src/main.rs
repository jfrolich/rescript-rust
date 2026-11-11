use js_reformat::{ReformatOptions, reformat};
use std::{
    collections::BTreeSet,
    env, fs,
    path::{Path, PathBuf},
    process::ExitCode,
};

fn files(root: &Path) -> Result<BTreeSet<PathBuf>, String> {
    fn visit(root: &Path, dir: &Path, paths: &mut BTreeSet<PathBuf>) -> std::io::Result<()> {
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let kind = entry.file_type()?;
            let path = entry.path();
            if kind.is_dir() {
                visit(root, &path, paths)?;
            } else if kind.is_file()
                && matches!(
                    path.extension().and_then(|s| s.to_str()),
                    Some("js" | "mjs" | "cjs" | "jsx")
                )
            {
                paths.insert(path.strip_prefix(root).unwrap().to_owned());
            }
        }
        Ok(())
    }
    let mut paths = BTreeSet::new();
    visit(root, root, &mut paths).map_err(|e| format!("{}: {e}", root.display()))?;
    Ok(paths)
}

fn load(
    root: &Path,
    path: &Path,
    formatted: bool,
    options: ReformatOptions,
) -> Result<String, String> {
    let full = root.join(path);
    let source = fs::read_to_string(&full).map_err(|e| format!("{}: {e}", full.display()))?;
    if formatted {
        Ok(source)
    } else {
        reformat(&source, options).map_err(|e| format!("{}: {e}", full.display()))
    }
}

// split_inclusive retains newline differences, including a missing final newline.
fn difference<'a>(a: &'a str, b: &'a str) -> (usize, Option<&'a str>, Option<&'a str>) {
    let mut a = a.split_inclusive('\n');
    let mut b = b.split_inclusive('\n');
    for line in 1.. {
        let (a, b) = (a.next(), b.next());
        if a != b || a.is_none() {
            return (line, a, b);
        }
    }
    unreachable!()
}

fn show_difference(path: &Path, a: Option<&str>, b: Option<&str>) {
    let (line, left, right) = match (a, b) {
        (Some(a), Some(b)) => difference(a, b),
        _ => (
            1,
            a.and_then(|s| s.split_inclusive('\n').next()),
            b.and_then(|s| s.split_inclusive('\n').next()),
        ),
    };
    println!(
        "{}:{line}{}",
        path.display(),
        if a.is_none() {
            " (missing reference)"
        } else if b.is_none() {
            " (missing candidate)"
        } else {
            ""
        }
    );
    println!(
        "  reference: {}",
        left.map_or("<missing/EOF>".into(), |s| format!("{s:?}"))
    );
    println!(
        "  candidate: {}",
        right.map_or("<missing/EOF>".into(), |s| format!("{s:?}"))
    );
}

fn run() -> Result<u8, String> {
    let mut options = ReformatOptions::default();
    let mut candidate_formatted = false;
    let mut args = Vec::new();
    for arg in env::args_os().skip(1) {
        if arg == "--strip-comments" {
            options.strip_comments = true;
        } else if arg == "--split-file" {
            options.split_file = true;
        } else if arg == "--drop-decoration-comments" {
            options.drop_decoration_comments = true;
        } else if arg == "--candidate-formatted" {
            candidate_formatted = true;
        } else {
            args.push(arg);
        }
    }
    let command = args.first().and_then(|s| s.to_str()).unwrap_or("");
    let expected = match command {
        "format" | "compare" => 3,
        "check" => 2,
        _ => 0,
    };
    if expected == 0 || args.len() != expected || (candidate_formatted && command != "compare") {
        return Err("Usage: js-reformat format <in-dir> <out-dir> | compare <reference-dir> <candidate-dir> [--candidate-formatted] | check <dir> [--strip-comments] [--split-file] [--drop-decoration-comments] (all commands)".into());
    }
    let root = Path::new(&args[1]);
    let paths = files(root)?;
    let mut failures = 0;
    let mut different = 0;
    if command == "compare" {
        let candidate = Path::new(&args[2]);
        let candidate_paths = files(candidate)?;
        let union: BTreeSet<_> = paths.union(&candidate_paths).collect();
        for path in &union {
            let left = paths
                .contains(*path)
                .then(|| load(root, path, false, options))
                .transpose();
            let right = candidate_paths
                .contains(*path)
                .then(|| load(candidate, path, candidate_formatted, options))
                .transpose();
            match (left, right) {
                (Ok(left), Ok(right)) => {
                    if left != right {
                        different += 1;
                        show_difference(path, left.as_deref(), right.as_deref());
                    }
                }
                (left, right) => {
                    failures += 1;
                    for e in [left.err(), right.err()].into_iter().flatten() {
                        eprintln!("{e}");
                    }
                }
            }
        }
        println!(
            "{} files, {different} different or missing, {failures} failed",
            union.len()
        );
    } else {
        // Snapshot the file list before writing, including for in-place formatting.
        for path in &paths {
            let result = load(root, path, false, options).and_then(|text| {
                if command == "check" {
                    if reformat(&text, options)? != text {
                        different += 1;
                        println!("{}: not a fixed point", path.display());
                    }
                } else {
                    let output = Path::new(&args[2]).join(path);
                    fs::create_dir_all(output.parent().unwrap())
                        .and_then(|()| fs::write(&output, text))
                        .map_err(|e| format!("{}: {e}", output.display()))?;
                }
                Ok(())
            });
            if let Err(e) = result {
                failures += 1;
                eprintln!("{}: {e}", path.display());
            }
        }
        println!(
            "{} files, {failures} failed, {different} not a fixed point",
            paths.len()
        );
    }
    Ok(if failures > 0 {
        2
    } else if different > 0 {
        1
    } else {
        0
    })
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => ExitCode::from(code),
        Err(e) => {
            eprintln!("{e}");
            ExitCode::from(2)
        }
    }
}
