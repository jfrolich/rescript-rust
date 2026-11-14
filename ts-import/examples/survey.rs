//! Imports whole packages and counts where ReScript says less than
//! TypeScript, by kind of gap.
//!
//!     cargo run --release --example survey -- /abs/project/Importer.res react node:fs ...
//!
//! The importer need not exist: it only says where module specifiers are
//! resolved from. One line per module, then the totals.
use std::collections::{BTreeMap, BTreeSet};

use rescript_ts_import::{Files, Item, Request, RequestKind, resolve};

#[derive(Default)]
struct Count {
    values: usize,
    types: usize,
    /// Values and types with at least one note.
    inexact: BTreeSet<String>,
    /// Per kind of gap: the values and types it affects.
    gaps: BTreeMap<&'static str, BTreeSet<String>>,
}

fn count_items(items: &[Item], count: &mut Count) {
    for item in items {
        match item {
            Item::Types(decls) => count.types += decls.len(),
            Item::External(_) => count.values += 1,
            Item::Module(_, items) => count_items(items, count),
        }
    }
}

fn main() {
    // Declaration files of large packages nest deeply.
    let survey = std::thread::Builder::new().stack_size(512 << 20).spawn(run).expect("thread");
    survey.join().expect("survey");
}

fn run() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (importer, modules) = (&args[0], &args[1..]);
    let mut total = Count::default();
    println!("{:<28} {:>7} {:>7} {:>8} {:>9}", "module", "values", "types", "inexact", "ms");
    for module in modules {
        let request = Request {
            module: module.clone(),
            kind: RequestKind::Module { local: "M".to_string() },
            scope: Vec::new(),
        };
        let resolution = match resolve(&Files::Os, importer, std::slice::from_ref(&request)) {
            Ok(resolution) => resolution,
            Err(message) => {
                println!("{module:<28} error: {message}");
                continue;
            }
        };
        let mut count = Count::default();
        match &resolution.expansions[0] {
            Ok(expansion) => {
                count_items(&expansion.items, &mut count);
                for note in &expansion.notes {
                    count.inexact.insert(note.subject.clone());
                    count.gaps.entry(note.gap.id()).or_default().insert(note.subject.clone());
                }
            }
            Err(message) => {
                println!("{module:<28} error: {message}");
                continue;
            }
        }
        println!(
            "{:<28} {:>7} {:>7} {:>8} {:>9.1}",
            module,
            count.values,
            count.types,
            count.inexact.len(),
            resolution.stats.micros as f64 / 1000.0
        );
        total.values += count.values;
        total.types += count.types;
        total.inexact.extend(count.inexact.iter().map(|subject| format!("{module}#{subject}")));
        for (gap, subjects) in count.gaps {
            let all = total.gaps.entry(gap).or_default();
            all.extend(subjects.iter().map(|subject| format!("{module}#{subject}")));
        }
    }
    let declarations = total.values + total.types;
    println!(
        "\n{} values and {} types; {} of them ({:.0}%) carry a note",
        total.values,
        total.types,
        total.inexact.len(),
        100.0 * total.inexact.len() as f64 / declarations.max(1) as f64
    );
    let mut gaps: Vec<(&str, usize)> = total.gaps.iter().map(|(gap, subjects)| (*gap, subjects.len())).collect();
    gaps.sort_by_key(|gap| std::cmp::Reverse(gap.1));
    println!("\ndeclarations affected, by kind of gap:");
    for (gap, n) in gaps {
        println!("{gap:<22} {n:>6} {:>5.1}%", 100.0 * n as f64 / declarations.max(1) as f64);
    }
}
