//! Command-line entry points for testing the compiler file by file.
//!
//! These are not shipped as separate executables. `rescript` runs them when it
//! is invoked under the name `bsc` or `res_parser_rust` (for example through a
//! symlink), so the parity scripts can drive the compiler linked into it.

pub mod bsc;
pub mod res_parser;
