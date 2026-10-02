//! Cached debug environment flags.
//!
//! These flags are process-level debugging toggles. Reading them through
//! `OnceLock` avoids repeated process-environment probing in compiler hot paths.

use std::sync::OnceLock;

fn enabled(flag: &'static OnceLock<bool>, name: &'static str) -> bool {
    *flag.get_or_init(|| std::env::var_os(name).is_some())
}

static RAW_FALLBACK_TRACE: OnceLock<bool> = OnceLock::new();
static SKIP_FOR_MULTIPLE_MATCH: OnceLock<bool> = OnceLock::new();
static SKIP_PATTERN_LOWER: OnceLock<bool> = OnceLock::new();
static DEBUG_OPEN_SIG_VALUES: OnceLock<bool> = OnceLock::new();
static DEBUG_STATICCATCH_RETURN: OnceLock<bool> = OnceLock::new();
static DEBUG_TAKE_RETURN_TAIL: OnceLock<bool> = OnceLock::new();
static DEBUG_COMPILE_TEST_RETURN: OnceLock<bool> = OnceLock::new();

/// Whether raw-lambda fallback tracing is enabled.
pub fn raw_fallback_trace() -> bool {
    enabled(&RAW_FALLBACK_TRACE, "RUST_RAW_FALLBACK_TRACE")
}

/// Whether tuple-scrutinee multiple-match lowering should be skipped.
pub fn skip_for_multiple_match() -> bool {
    enabled(&SKIP_FOR_MULTIPLE_MATCH, "RUST_SKIP_FOR_MULTIPLE_MATCH")
}

/// Whether pattern-lowering propagation should be skipped.
pub fn skip_pattern_lower() -> bool {
    enabled(&SKIP_PATTERN_LOWER, "RUST_SKIP_PATTERN_LOWER")
}

/// Whether opened signature values should be traced.
pub fn debug_open_sig_values() -> bool {
    enabled(&DEBUG_OPEN_SIG_VALUES, "RUST_DEBUG_OPEN_SIG_VALUES")
}

/// Whether staticcatch return lowering should be traced.
pub fn debug_staticcatch_return() -> bool {
    enabled(&DEBUG_STATICCATCH_RETURN, "RUST_DEBUG_STATICCATCH_RETURN")
}

/// Whether return-tail extraction should be traced.
pub fn debug_take_return_tail() -> bool {
    enabled(&DEBUG_TAKE_RETURN_TAIL, "RUST_DEBUG_TAKE_RETURN_TAIL")
}

/// Whether compile-test-return lowering should be traced.
pub fn debug_compile_test_return() -> bool {
    enabled(&DEBUG_COMPILE_TEST_RETURN, "RUST_DEBUG_COMPILE_TEST_RETURN")
}

static DEBUG_PERS_STRUCT: OnceLock<bool> = OnceLock::new();
static DEBUG_PERSISTENT_SOURCE_FALLBACK: OnceLock<bool> = OnceLock::new();
static DEBUG_STORE: OnceLock<bool> = OnceLock::new();
static DEBUG_SIG_VALUE: OnceLock<Option<String>> = OnceLock::new();

/// Whether persistent-structure lookups should be traced.
pub fn debug_pers_struct() -> bool {
    enabled(&DEBUG_PERS_STRUCT, "RUST_DEBUG_PERS_STRUCT")
}

/// Whether persistent source fallbacks should be traced.
pub fn debug_persistent_source_fallback() -> bool {
    enabled(
        &DEBUG_PERSISTENT_SOURCE_FALLBACK,
        "RUST_DEBUG_PERSISTENT_SOURCE_FALLBACK",
    )
}

/// Whether thread-store internalization should be traced.
pub fn debug_store() -> bool {
    enabled(&DEBUG_STORE, "RUST_DEBUG_STORE")
}

/// Comma-separated value names whose CMI signature reads should be traced.
pub fn debug_sig_value() -> Option<&'static str> {
    DEBUG_SIG_VALUE
        .get_or_init(|| std::env::var("RUST_DEBUG_SIG_VALUE").ok())
        .as_deref()
}
