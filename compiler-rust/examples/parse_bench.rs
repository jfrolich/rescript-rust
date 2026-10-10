// Local benchmark: parse every file listed in argv[1] (one path per line), N times.
use rescript_compiler::parser::{module, Parser};
fn main() {
    let list = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();
    let reps: usize = std::env::args().nth(2).map(|s| s.parse().unwrap()).unwrap_or(3);
    let files: Vec<(String, String)> = list
        .lines()
        .map(|p| (p.to_string(), String::from_utf8_lossy(&std::fs::read(p).unwrap()).into_owned()))
        .collect();
    let bytes: usize = files.iter().map(|f| f.1.len()).sum();
    for _ in 0..reps {
        let t = std::time::Instant::now();
        let mut n = 0usize;
        for (path, src) in &files {
            let mut parser = Parser::new(path.clone(), src);
            if path.ends_with(".resi") {
                let s = module::parse_signature(&mut parser);
                n += s.len();
            } else {
                let s = module::parse_structure(&mut parser);
                n += s.len();
            }
        }
        let e = t.elapsed();
        eprintln!("parsed {} files {} MB in {:?} ({:.1} MB/s) items={}", files.len(), bytes / 1_000_000, e, bytes as f64 / 1e6 / e.as_secs_f64(), n);
    }
}
