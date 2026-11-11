//! Prints what `%ts` imports expand to.
//!
//!     cargo run --example show -- /abs/dir/Importer.res ./api.ts [export...]
//!
//! Without export names the whole module is imported. A name starting with
//! an upper-case letter is imported as a type.
use rescript_ts_import::{Files, Request, RequestKind, ValueImport, lower_ident, resolve};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (importer, module, names) = (&args[0], &args[1], &args[2..]);
    let mut requests = Vec::new();
    if names.is_empty() {
        requests.push(Request {
            module: module.clone(),
            kind: RequestKind::Module { local: "M".to_string() },
            scope: Vec::new(),
        });
    }
    for name in names {
        let kind = if name.as_bytes()[0].is_ascii_uppercase() {
            RequestKind::Type { export: name.clone(), local: lower_ident(name) }
        } else {
            RequestKind::Values(vec![ValueImport { export: name.clone(), local: lower_ident(name) }])
        };
        requests.push(Request { module: module.clone(), kind, scope: Vec::new() });
    }
    // A second run shows what an import costs once the library is parsed.
    let first = std::time::Instant::now();
    let _ = resolve(&Files::Os, importer, &requests);
    eprintln!("first run: {:?}", first.elapsed());
    let start = std::time::Instant::now();
    match resolve(&Files::Os, importer, &requests) {
        Err(message) => eprintln!("error: {message}"),
        Ok(resolution) => {
            for expansion in &resolution.expansions {
                match expansion {
                    Ok(expansion) => {
                        print!("{}", expansion.code());
                        for note in &expansion.notes {
                            println!(
                                "// note [{}] {} ({}): {} -- `{}`",
                                note.gap.id(),
                                note.subject,
                                note.path,
                                note.message,
                                note.ts
                            );
                        }
                    }
                    Err(message) => println!("// error: {message}"),
                }
            }
            eprintln!("{:?} in {:?}", resolution.stats, start.elapsed());
            let full = rescript_ts_import::full_check(&Files::Os, importer, std::slice::from_ref(module));
            eprintln!("full check of the same files: {full:?}");
        }
    }
}
