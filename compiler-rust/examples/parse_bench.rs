//! Parse-only benchmark; see scripts/bench_parse.sh for instruction counts.
use rescript_compiler::intern::StrIdx;
use rescript_compiler::parser::{Parser, Scanner, Token, module};
use rescript_compiler::source_text::latin1_bytes_to_string;
use std::hint::black_box;
use std::path::{Path, PathBuf};
use std::time::Instant;

#[derive(Clone, Copy, Debug, PartialEq)]
enum Mode {
    Scan,
    Parse,
}

fn arguments(mut args: impl Iterator<Item = String>) -> Result<(Mode, usize, Vec<PathBuf>), String> {
    let (mut mode, mut iterations, mut paths) = (Mode::Parse, 1, Vec::new());
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--iterations" => {
                iterations = args
                    .next()
                    .and_then(|s| s.parse().ok())
                    .filter(|&n| n > 0)
                    .ok_or("--iterations requires a positive integer")?;
            }
            "--mode" => {
                mode = match args.next().as_deref() {
                    Some("scan") => Mode::Scan,
                    Some("parse") => Mode::Parse,
                    _ => return Err("--mode requires scan or parse".into()),
                };
            }
            "--" => {
                paths.extend(args.map(PathBuf::from));
                break;
            }
            _ if arg.starts_with('-') => return Err(format!("unknown option: {arg}")),
            _ => paths.push(PathBuf::from(arg)),
        }
    }
    if paths.is_empty() {
        return Err(
            "usage: parse_bench [--iterations N] [--mode scan|parse] FILE_OR_DIR...".into(),
        );
    }
    Ok((mode, iterations, paths))
}

fn collect(path: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
    // Do not follow symlinks: directory cycles must not change the corpus.
    let meta = std::fs::symlink_metadata(path)?;
    if meta.is_dir() {
        for entry in std::fs::read_dir(path)? {
            collect(&entry?.path(), files)?;
        }
    } else if meta.is_file()
        && matches!(
            path.extension().and_then(|s| s.to_str()),
            Some("res" | "resi")
        )
    {
        files.push(path.canonicalize()?);
    }
    Ok(())
}

fn line_count(bytes: &[u8]) -> usize {
    bytes.iter().filter(|&&b| b == b'\n').count()
        + usize::from(!bytes.is_empty() && !bytes.ends_with(b"\n"))
}

fn measure_file(mode: Mode, path: &str, source: &str) -> usize {
    match mode {
        Mode::Scan => {
            let mut scanner = Scanner::new(StrIdx::from_raw(0), source);
            loop {
                let result = black_box(scanner.scan());
                if result.token == Token::Eof {
                    break;
                }
            }
            scanner.diagnostics().len()
        }
        Mode::Parse => {
            // The build's parser entry points, with locations, but no frontend.
            let mut parser = Parser::new(path, source);
            if path.ends_with(".resi") {
                black_box(module::parse_signature(&mut parser));
            } else {
                black_box(module::parse_structure(&mut parser));
            }
            parser.diagnostics().len()
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let (mode, iterations, paths) = arguments(std::env::args().skip(1))?;
    let mut files = Vec::new();
    for path in paths {
        collect(&path, &mut files)?;
    }
    files.sort();
    files.dedup();
    if files.is_empty() {
        return Err("no .res or .resi files found".into());
    }
    let (mut lines, mut bytes) = (0usize, 0usize);
    let sources = files
        .iter()
        .map(|path| {
            let raw = std::fs::read(path)?;
            lines += line_count(&raw);
            bytes += raw.len();
            Ok((
                path.to_string_lossy().into_owned(),
                latin1_bytes_to_string(raw),
            ))
        })
        .collect::<std::io::Result<Vec<_>>>()?;
    let total_lines = lines.checked_mul(iterations).ok_or("line count overflow")?;
    let start = Instant::now();
    let mut errors = 0usize;
    for _ in 0..iterations {
        for (path, source) in &sources {
            errors += measure_file(mode, path, source);
        }
    }
    let elapsed = start.elapsed().as_secs_f64();
    println!(
        "files={} lines={} bytes={} parse_errors={} total_ms={:.3} ns_per_line={:.3}",
        files.len(),
        lines,
        bytes,
        errors,
        elapsed * 1e3,
        if total_lines == 0 {
            0.0
        } else {
            elapsed * 1e9 / total_lines as f64
        }
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn options_and_lines() {
        assert_eq!(
            arguments(["a.res".into()].into_iter()).unwrap(),
            (Mode::Parse, 1, vec![PathBuf::from("a.res")])
        );
        for args in [
            vec!["--iterations", "0", "a.res"],
            vec!["--mode", "invalid"],
            vec![],
        ] {
            assert!(arguments(args.into_iter().map(str::to_owned)).is_err());
        }
        for (source, lines) in [("", 0), ("a", 1), ("a\n", 1), ("a\nb", 2), ("\r\n\n", 2)] {
            assert_eq!(line_count(source.as_bytes()), lines);
        }
    }

    #[test]
    fn entry_points_and_errors() {
        assert_eq!(measure_file(Mode::Parse, "a.res", "let x = 1"), 0);
        assert_eq!(measure_file(Mode::Parse, "a.resi", "let x: int"), 0);
        assert!(measure_file(Mode::Parse, "a.res", "let =") > 0);
        assert_eq!(measure_file(Mode::Scan, "a.res", "let x = 1"), 0);
        assert!(measure_file(Mode::Scan, "a.res", "/*") > 0);
    }

    #[test]
    fn collects_only_sources_recursively() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::create_dir(dir.path().join("nested")).unwrap();
        for name in ["b.res", "nested/a.resi", "ignored.js"] {
            std::fs::write(dir.path().join(name), "").unwrap();
        }
        let mut files = Vec::new();
        collect(dir.path(), &mut files).unwrap();
        files.sort();
        assert_eq!(files.len(), 2);
        assert!(files[0].ends_with("b.res"));
        assert!(files[1].ends_with("nested/a.resi"));
    }
}
