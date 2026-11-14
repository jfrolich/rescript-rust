//! Opt-in AST emitter. Unsupported modules are printed entirely by the legacy path.
mod build;
mod literal;
mod naming;
pub(crate) use naming::{FreeLists, NameStats, Printed, Subject, Tables, compare_with_pass};
#[cfg(test)]
pub(crate) use naming::pass_tables;
mod program;
mod raw;
pub use raw::RawSegment;
pub mod sourcemap;
mod walk;

use crate::js_ir::{ModulePathResolver, arena::JsDepsProgram};
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

/// The first construct for which the experimental emitter has no exact rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unsupported(pub &'static str);

/// Printer selection; the opt-in variant owns its coverage counters.
#[derive(Clone, Debug, Default)]
pub enum PrinterMode {
    /// Byte-identical legacy output (the default).
    #[default]
    Legacy,
    /// Experimental AST output, with whole-file fallback.
    Oxc(Arc<PrinterStats>),
}

impl PrinterMode {
    /// Read the opt-in environment variable when creating compilation options.
    pub fn from_env() -> Self {
        Self::from_value(std::env::var("RESCRIPT_JS_PRINTER").ok().as_deref())
    }

    fn from_value(value: Option<&str>) -> Self {
        match value {
            Some("oxc") => Self::Oxc(Arc::default()),
            _ => Self::Legacy,
        }
    }
}

/// Per-compilation-option counters, shared by workers but never global.
#[derive(Debug, Default)]
pub struct PrinterStats {
    coverage: Mutex<Coverage>,
    raw_audit: Option<Mutex<Vec<RawSegment>>>,
}

/// A snapshot of complete-file support and first fallback reasons.
#[derive(Clone, Debug, Default)]
pub struct Coverage {
    /// Number of outputs emitted entirely by oxc.
    pub supported: usize,
    /// Number of legacy fallbacks by first unsupported construct.
    pub unsupported: BTreeMap<&'static str, usize>,
}

impl PrinterStats {
    /// Enable IR-derived raw-segment evidence for the oracle only. Ordinary
    /// compilation does not allocate or retain this diagnostic data.
    pub fn with_raw_audit() -> Self {
        Self {
            coverage: Mutex::default(),
            raw_audit: Some(Mutex::default()),
        }
    }

    pub(crate) fn raw_audit_buffer(&self) -> Option<Vec<RawSegment>> {
        self.raw_audit.as_ref().map(|_| Vec::new())
    }

    pub(crate) fn record_raw(&self, raw: Option<Vec<RawSegment>>) {
        if let (Some(target), Some(raw)) = (&self.raw_audit, raw) {
            *target.lock().expect("raw audit lock poisoned") = raw;
        }
    }

    /// Take the most recently emitted file's raw segments, in output order.
    pub fn take_raw_segments(&self) -> Vec<RawSegment> {
        self.raw_audit
            .as_ref()
            .map(|raw| std::mem::take(&mut *raw.lock().expect("raw audit lock poisoned")))
            .unwrap_or_default()
    }

    /// Count one attempted output.
    pub fn record(&self, result: &Result<(String, Option<String>), Unsupported>) {
        let mut counts = self
            .coverage
            .lock()
            .expect("printer coverage lock poisoned");
        match result {
            Ok(_) => counts.supported += 1,
            Err(reason) => *counts.unsupported.entry(reason.0).or_default() += 1,
        }
    }

    /// Opt-in per-output evidence for build-level parity coverage. Immutable
    /// outcomes prevent repeated invocations from hiding an earlier fallback.
    pub(crate) fn report_output(
        &self,
        result: &Result<(String, Option<String>), Unsupported>,
        source: Option<&std::path::Path>,
        output: Option<&std::path::Path>,
    ) -> anyhow::Result<()> {
        use std::hash::{Hash, Hasher};
        let Some(directory) = std::env::var_os("RESCRIPT_JS_PRINTER_STATS") else {
            return Ok(());
        };
        let Some(output) = output else {
            return Ok(());
        };
        let absolute = |p: &std::path::Path| -> std::io::Result<std::path::PathBuf> {
            Ok(if p.is_absolute() {
                p.into()
            } else {
                std::env::current_dir()?.join(p)
            })
        };
        let output = absolute(output)?;
        let source = source.map(absolute).transpose()?;
        let reason = result.as_ref().err().map(|e| e.0);
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        output.hash(&mut hash);
        reason.hash(&mut hash);
        let directory = std::path::Path::new(&directory);
        std::fs::create_dir_all(directory)?;
        let path = directory.join(format!("{:016x}.json", hash.finish()));
        let mut file = match std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
        {
            Ok(file) => file,
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => return Ok(()),
            Err(e) => return Err(e.into()),
        };
        serde_json::to_writer(
            &mut file,
            &serde_json::json!({
                "source": source, "output": output, "emitted": result.is_ok(), "unsupported": reason,
            }),
        )?;
        Ok(())
    }

    /// Read counters without resetting them.
    pub fn snapshot(&self) -> Coverage {
        self.coverage
            .lock()
            .expect("printer coverage lock poisoned")
            .clone()
    }
}

/// Emit a complete module, or return its first unsupported construct.
pub fn emit(
    program: &JsDepsProgram,
    resolver: &ModulePathResolver,
    directives: &[String],
    debug: bool,
    jsx_preserve: bool,
    header: bool,
) -> Result<(String, Option<String>), Unsupported> {
    program::emit(
        program,
        resolver,
        directives,
        program::FileOptions { debug, jsx_preserve, header },
        None,
        None,
    )
}

pub(crate) fn emit_audited(
    program: &JsDepsProgram,
    resolver: &ModulePathResolver,
    directives: &[String],
    debug: bool,
    jsx_preserve: bool,
    header: bool,
    audit: Option<&mut Vec<RawSegment>>,
) -> Result<(String, Option<String>), Unsupported> {
    program::emit(
        program,
        resolver,
        directives,
        program::FileOptions { debug, jsx_preserve, header },
        None,
        audit,
    )
}

/// Emit with source maps, retaining whole-file fallback on unsupported mappings.
#[allow(clippy::too_many_arguments)]
pub fn emit_with_source_map(
    program: &JsDepsProgram, resolver: &ModulePathResolver, directives: &[String],
    debug: bool, jsx_preserve: bool, header: bool, options: &sourcemap::Options<'_>,
) -> Result<(String, Option<String>), Unsupported> {
    program::emit(
        program,
        resolver,
        directives,
        program::FileOptions { debug, jsx_preserve, header },
        Some(options),
        None,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn selection_is_explicit_and_legacy_by_default() {
        for value in [None, Some("legacy"), Some(""), Some("unknown")] {
            assert!(matches!(
                PrinterMode::from_value(value),
                PrinterMode::Legacy
            ));
        }
        assert!(matches!(
            PrinterMode::from_value(Some("oxc")),
            PrinterMode::Oxc(_)
        ));
    }

    #[test]
    fn counters_belong_to_the_options() {
        let stats = PrinterStats::default();
        stats.record(&Err(Unsupported("function")));
        stats.record(&Ok((String::new(), None)));
        assert_eq!(stats.snapshot().supported, 1);
        assert_eq!(stats.snapshot().unsupported["function"], 1);
        assert_eq!(PrinterStats::default().snapshot().supported, 0);
    }
}

#[cfg(test)]
mod oracle_tests {
    use super::*;
    use crate::driver::{CompilerOptions, compile_source_to_js_with_options};
    use js_reformat::{ReformatOptions, reformat};

    fn oracle(source: &str, commonjs: bool) {
        let stats = Arc::new(PrinterStats::with_raw_audit());
        let mut options = CompilerOptions {
            include_paths: vec![
                std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("../packages/@rescript/runtime/lib/rescript"),
            ],
            js_printer: PrinterMode::Legacy,
            output_module_format: Some(if commonjs {
                crate::js_ir::ModuleFormat::CommonJs
            } else {
                crate::js_ir::ModuleFormat::EsModule
            }),
            ..CompilerOptions::default()
        };
        let legacy = compile_source_to_js_with_options(source, "Emitter.res", &options).unwrap();
        options.js_printer = PrinterMode::Oxc(stats.clone());
        let actual = compile_source_to_js_with_options(source, "Emitter.res", &options).unwrap();
        assert_eq!(stats.snapshot().supported, 1, "{source}: {:?}", stats.snapshot());
        let mode = ReformatOptions {
            split_file: true,
            drop_decoration_comments: true,
            ..Default::default()
        };
        let segments = stats.take_raw_segments();
        if source.contains("%raw(") {
            assert!(
                !segments.is_empty(),
                "raw fixture must exercise substitution"
            );
        }
        let normalized = reformat(&actual, mode).unwrap();
        assert_eq!(
            reformat(&legacy, mode).unwrap(),
            if segments.is_empty() {
                actual.clone()
            } else {
                normalized
            },
            "{source}"
        );
        let mut masked = String::new();
        let mut cursor = 0;
        for segment in &segments {
            assert_eq!(
                &actual[segment.text_range.clone()],
                segment.text,
                "IR raw text: {source}"
            );
            assert!(segment.replacement_range.start >= cursor);
            masked.push_str(&actual[cursor..segment.replacement_range.start]);
            masked.push_str(&segment.placeholder);
            cursor = segment.replacement_range.end;
        }
        masked.push_str(&actual[cursor..]);
        assert_eq!(
            reformat(&masked, mode).unwrap(),
            masked,
            "masked fixed point: {source}"
        );
    }

    #[test]
    fn remaining_expressions_source_oracle() {
        for source in [
            "let f = @this self => self + 1",
            "let f = @this (self: int) => 1",
            "let f = x => y => z => x + y + z",
            "let f = x => async y => x + y",
            "type rest = {b: int}; type t = {a: int, b: int}; let f = (r: t) => {let {a, ...rest as other} = r; (a, other)}",
            "let f = x => Some(x)",
            "let f = x => x ++ (x ++ x)",
        ] {
            for commonjs in [false, true] {
                oracle(source, commonjs);
            }
        }
    }

    #[test]
    fn core_source_oracle() {
        for source in [
            "let value = 42",
            "let text = \"hello\"",
            "let yes = true",
            "let empty = ()",
            "let identity = x => x",
            "let select = (condition, yes, no) => if condition {yes} else {no}",
            "let values = [1, 2, 3]",
            "type t = int",
            "let default = 7",
        ] {
            for commonjs in [false, true] {
                oracle(source, commonjs);
            }
        }
    }
    #[test]
    fn placeholder_in_non_raw_string_falls_back_without_replacement() {
        let source = "let text = \"__rescript_raw$0$\"; let value = %raw(`({x:1})`)";
        let stats = Arc::new(PrinterStats::with_raw_audit());
        let mut options = CompilerOptions::default();
        let legacy = compile_source_to_js_with_options(source, "Collision.res", &options).unwrap();
        options.js_printer = PrinterMode::Oxc(stats.clone());
        let actual = compile_source_to_js_with_options(source, "Collision.res", &options).unwrap();
        assert_eq!(actual, legacy);
        assert_eq!(stats.snapshot().unsupported["raw placeholder collision"], 1);
        assert!(stats.take_raw_segments().is_empty());
    }

    #[test]
    fn control_flow_source_oracle() {
        for source in [
            "let f = n => { for i in 0 to n { effect(i) } }",
            "let f = n => { for i in n downto 0 { effect(i) } }",
            "let f = n => { while condition(n) { effect(n) } }",
            "type box = {mutable value: int}; let f = n => { let x = {value: n}; x.value = n; effect(x.value) }",
            "let f = n => switch n { | 0 => effect(0) | 1 => effect(1) | _ => effect(n) }",
            "external raise: exn => 'a = \"%raise\"; let f = e => raise(e)",
            "let f = n => { effect(n); effect(n) }",
        ] {
            for commonjs in [false, true] {
                oracle(
                    &format!(
                        "@val external effect: int => unit = \"effect\"; @val external condition: int => bool = \"condition\"; {source}"
                    ),
                    commonjs,
                );
            }
        }
    }
    #[test]
    fn scoped_names_source_oracle() {
        for source in [
            "let x = 1; let x = 2; let y = x",
            "let f = x => { let x = add(x, 1); x }",
            "let f = x => y => add(x, y)",
            "let f = x => { let g = x => add(x, 1); add(g(x), x) }",
            "let f = f => add(f, 1)",
            "let f = (c, x) => if c { let x = add(x, 1); x } else { let x = add(x, -1); x }",
            "let default = 1; let default = add(default, 1)",
            "let f = x => add(x, 1); let g = x => add(x, 2)",
            "@val external x: int = \"x\"; let f = x => add(x, 1); let g = y => add(x, y)",
        ] {
            for commonjs in [false, true] {
                oracle(
                    &format!("external add: (int, int) => int = \"%addint\"; {source}"),
                    commonjs,
                );
            }
        }
    }
    #[test]
    fn block_payloads_keep_scoped_names() {
        for source in [
            "type t = {left: int, right: int, missing?: int}; let f = x => { let y = x; let x = add(x, 1); {left: y, right: x} }",
            "type t = A(int, int) | B; let f = x => { let y = x; let x = add(x, 1); A(y, x) }",
            "type t = A({left: int, right: int, missing?: int}) | B; let f = x => { let y = x; let x = add(x, 1); A({left: y, right: x}) }",
            "let f = x => { let y = x; let x = add(x, 1); (y, x) }",
            "let f = (x, tail) => { let y = x; let x = add(x, 1); list{y, x, ...tail} }",
            "let f = x => { let x = add(x, 1); #Value(x) }",
            "let f = x => { module M = { let x = add(x, 1) }; M.x }",
        ] {
            for commonjs in [false, true] {
                oracle(
                    &format!("external add: (int, int) => int = \"%addint\"; {source}"),
                    commonjs,
                );
            }
        }
    }
    #[test]
    fn text_payloads_source_oracle() {
        for source in [
            "let value = `hello`",
            "let f = x => `hello ${x}!`",
            "let f = x => `a\\n${x}\\`end`",
            "@val external tag: taggedTemplate<string, string> = \"tag\"; let f = x => tag`hello ${x}!`",
            "@val external consume: (@as(json`{hello: [1, 2]}`) _) => int = \"consume\"; let value = consume()",
            "let f = @directive(\"'use server'\") x => x",
            "let f = x => { let g = @directive(\"'use cache'\") y => y; g(x) }",
            "@module({from: `./data.json`, with: {type_: `json`, \\\"some-key\": `value`}}) external data: int = \"default\"; let value = data",
            "type t = A | B; let value = A",
            "exception E",
            "let value = `café 😀`",
            "@val external tag: taggedTemplate<string, string> = \"tag\"; let f = x => tag`\\unicode ${x} end`",
        ] {
            for commonjs in [false, true] {
                oracle(source, commonjs);
            }
        }
    }
    #[test]
    fn verbatim_raw_snippets_are_preserved() {
        for source in [
            "let value = %raw(`({answer:42})`)",
            "let f = () => %raw(`({answer:42})`)",
            "let f = x => %raw(`console.log(  1 )`)",
            "let value = %raw(`({message: \"__rescript_raw$0$\"})`)",
            "let value = %raw(`({answer:42,\n  other:43})`)",
            "%%raw(`console.log(1);\n  console.log(2);`)",
            "@val external existing: int = \"__rescript_raw$0$\"; let value = (existing, %raw(`({x:1})`))",
            "let value = (%raw(`({x:1})`), %raw(`({x:1})`))",
            "let value = %raw(`({text: \"café 😀\"})`)",
            "let value = %raw(`function(x){return x}`)",
            "%%raw(`console.log(  1 )`)\nlet value = 1",
            "%%raw(`// leading comment`)\nlet value = 1",
            "%%raw(`/* block comment */`)\nlet value = 1",
            "let f = () => %raw(`(/* inside function */ doSomething())`)",
            "let value = %raw(`(/* expression comment */ 1)`)",
            "%%raw(`console.log(/* argument comment */ 1)`)",
            "%%raw(`console.log(1) // trailing comment`)",
        ] {
            for commonjs in [false, true] {
                oracle(source, commonjs);
            }
        }
    }
}
