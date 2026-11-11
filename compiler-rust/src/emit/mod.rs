//! Opt-in AST emitter. Unsupported modules are printed entirely by the legacy path.
mod build;
mod naming;
mod program;
mod walk;

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use crate::js_ir::{ModulePathResolver, arena::JsDepsProgram};

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
        self.0.lock().expect("printer coverage lock poisoned").clone()
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
    program::emit(program, resolver, directives, debug, jsx_preserve, header)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn selection_is_explicit_and_legacy_by_default() {
        for value in [None, Some("legacy"), Some(""), Some("unknown")] {
            assert!(matches!(PrinterMode::from_value(value), PrinterMode::Legacy));
        }
        assert!(matches!(PrinterMode::from_value(Some("oxc")), PrinterMode::Oxc(_)));
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
