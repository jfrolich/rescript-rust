//! Opt-in AST emitter. Unsupported modules are printed entirely by the legacy path.
mod build;
mod literal;
mod naming;
mod program;
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
pub struct PrinterStats(Mutex<Coverage>);

/// A snapshot of complete-file support and first fallback reasons.
#[derive(Clone, Debug, Default)]
pub struct Coverage {
    /// Number of outputs emitted entirely by oxc.
    pub supported: usize,
    /// Number of legacy fallbacks by first unsupported construct.
    pub unsupported: BTreeMap<&'static str, usize>,
}

impl PrinterStats {
    /// Count one attempted output.
    pub fn record(&self, result: &Result<(String, Option<String>), Unsupported>) {
        let mut counts = self.0.lock().expect("printer coverage lock poisoned");
        match result {
            Ok(_) => counts.supported += 1,
            Err(reason) => *counts.unsupported.entry(reason.0).or_default() += 1,
        }
    }

    /// Read counters without resetting them.
    pub fn snapshot(&self) -> Coverage {
        self.0
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
    program::emit(program, resolver, directives, debug, jsx_preserve, header, None)
}

/// Emit with source maps, retaining whole-file fallback on unsupported mappings.
#[allow(clippy::too_many_arguments)]
pub fn emit_with_source_map(
    program: &JsDepsProgram, resolver: &ModulePathResolver, directives: &[String],
    debug: bool, jsx_preserve: bool, header: bool, options: &sourcemap::Options<'_>,
) -> Result<(String, Option<String>), Unsupported> {
    program::emit(program, resolver, directives, debug, jsx_preserve, header, Some(options))
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
        let stats = Arc::new(PrinterStats::default());
        let mut options = CompilerOptions {
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
        assert_eq!(reformat(&legacy, mode).unwrap(), actual, "{source}");
        assert_eq!(
            reformat(&actual, mode).unwrap(),
            actual,
            "fixed point: {source}"
        );
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
    fn comment_bearing_raw_snippets_fall_back_without_loss() {
        for source in [
            "%%raw(`// leading comment`)\nlet value = 1",
            "%%raw(`/* block comment */`)\nlet value = 1",
            "let f = () => %raw(`(/* inside function */ doSomething())`)",
            "let value = %raw(`(/* expression comment */ 1)`)",
            "%%raw(`console.log(/* argument comment */ 1)`)",
            "%%raw(`console.log(1) // trailing comment`)",
        ] {
            let stats = Arc::new(PrinterStats::default());
            let mut options = CompilerOptions {
                js_printer: PrinterMode::Legacy,
                ..CompilerOptions::default()
            };
            let legacy =
                compile_source_to_js_with_options(source, "Comments.res", &options).unwrap();
            options.js_printer = PrinterMode::Oxc(stats.clone());
            let actual =
                compile_source_to_js_with_options(source, "Comments.res", &options).unwrap();
            assert_eq!(actual, legacy);
            assert_eq!(stats.snapshot().supported, 0, "{source}");
            assert_eq!(stats.snapshot().unsupported.values().sum::<usize>(), 1);
        }
    }
}
