//! Cached debug environment flags.
//!
//! These flags are process-level tracing toggles; none of them changes
//! compiler output. Reading them through `OnceLock` avoids repeated
//! process-environment probing in compiler hot paths.

use std::sync::OnceLock;

fn enabled(flag: &'static OnceLock<bool>, name: &'static str) -> bool {
    *flag.get_or_init(|| std::env::var_os(name).is_some())
}

static DEBUG_PERS_STRUCT: OnceLock<bool> = OnceLock::new();
static DEBUG_PERSISTENT_SOURCE_FALLBACK: OnceLock<bool> = OnceLock::new();

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
