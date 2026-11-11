//! Compile-time macros.
//!
//! A macro is a ReScript function the compiler runs while compiling another
//! file; it returns code. The design is in `docs/comptime/README.md`. This
//! module holds the compiler's half:
//!
//! - [`quote`] rewrites the quotes of a macro's own file (`%code(...)`,
//!   `%type(...)`, `%pat(...)`) into calls that build the quoted source text.
//! - [`discover`] is the type checker's side: it recognizes the places a
//!   macro is used, asks the engine to run it, and records the result as an
//!   edit of the source text.
//! - [`reflect`] answers a macro's questions about types.
//! - [`expand`] drives it: parse, type check, apply the edits, repeat until a
//!   pass finds nothing to expand. The compiler then compiles the expanded
//!   source like any other file, so a file without macros takes the path it
//!   always took.
//! - [`MacroHost`] is the JavaScript engine that runs macro code. The native
//!   build embeds QuickJS ([`quickjs`]); the browser build uses the page's
//!   own engine.

pub mod discover;
pub mod edit;
pub mod expand;
#[cfg(feature = "macro-quickjs")]
pub mod quickjs;
pub mod quote;
pub mod reflect;

/// The engine-side script: module loader and call entry point.
pub const HOST_JS: &str = include_str!("host.js");

/// The runtime module the macro API lives in.
pub const MACRO_MODULE: &str = "Macro";

/// A JavaScript engine that runs macro code.
///
/// `call` takes one JSON request and returns the JSON response of
/// `__rescript_macro_call` in `host.js`. The engine finds the compiled
/// JavaScript of a module by name; how is up to the embedder.
pub trait MacroHost: Send + Sync {
    fn call(&self, request: &str) -> Result<String, String>;
}

/// Call the engine with a request built from the compiler's text.
///
/// The compiler keeps source text as one `char` per byte of the file, so
/// that every offset is a byte offset; the engine works with the text those
/// bytes encode. Everything that crosses is converted here: the request to
/// real text, the response back to one `char` per byte.
pub(crate) fn call_host(host: &dyn MacroHost, request: &str) -> Result<String, String> {
    let response = host.call(&crate::source_text::decode_internal_utf8(request))?;
    Ok(crate::source_text::latin1_bytes_to_string(response.into_bytes()))
}

impl std::fmt::Debug for dyn MacroHost {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("MacroHost")
    }
}

/// Marker error of a compilation that met a macro while macro expansion was
/// off. The caller expands the source with [`expand::expand_source`] and
/// compiles the result.
#[derive(Debug)]
pub struct MacroExpansionRequired;

impl std::fmt::Display for MacroExpansionRequired {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("this file uses macros and must be expanded before it is compiled")
    }
}

impl std::error::Error for MacroExpansionRequired {}

/// Whether an extension or attribute name is a module path (`Json.encode`),
/// which is how a macro is named. PPX extensions and built-in attributes
/// start with a lowercase letter.
pub fn is_macro_name(name: &str) -> bool {
    name.starts_with(|c: char| c.is_ascii_uppercase())
}
