//! The ReScript declarations for every TypeScript feature in
//! `fixtures/features.ts`, compared with `fixtures/features.res.txt`.
//!
//! Run with `UPDATE_EXPECTED=1` to rewrite the expected file.

use rescript_ts_import::{Files, Request, RequestKind, resolve};

fn fixture(name: &str) -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name)
}

pub fn expand_features() -> String {
    let source = std::fs::read_to_string(fixture("features.ts")).unwrap();
    let files = Files::Memory(vec![("/app/features.ts".to_string(), source)]);
    let requests = [Request {
        module: "./features.ts".to_string(),
        kind: RequestKind::Module { local: "Features".to_string() },
        scope: Vec::new(),
    }];
    let resolution = resolve(&files, "/app/Demo.res", &requests).unwrap();
    let expansion = resolution.expansions.into_iter().next().unwrap().unwrap();
    let mut out = expansion.code();
    out.push_str("\n// Where ReScript says less than TypeScript:\n");
    for note in &expansion.notes {
        let place = if note.path.is_empty() { note.subject.clone() } else { format!("{} ({})", note.subject, note.path) };
        out.push_str(&format!("// [{}] {}: `{}`: {}\n", note.gap.id(), place, note.ts, note.message));
    }
    out
}

#[test]
fn features() {
    let actual = expand_features();
    let expected_path = fixture("features.res.txt");
    if std::env::var_os("UPDATE_EXPECTED").is_some() {
        std::fs::write(&expected_path, &actual).unwrap();
        return;
    }
    let expected = std::fs::read_to_string(&expected_path).unwrap_or_default();
    assert!(
        actual == expected,
        "the declarations for tests/fixtures/features.ts changed; run with UPDATE_EXPECTED=1 and review the diff\n{actual}"
    );
}
