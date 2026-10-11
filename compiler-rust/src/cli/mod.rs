//! Command-line entry points for testing the compiler file by file.
//!
//! These are not shipped as separate executables: the hidden `rescript bsc` and
//! `rescript res-parser` commands run them, so the parity scripts can drive the
//! compiler linked into `rescript` against the OCaml reference compiler.

pub mod bsc;
pub mod res_parser;
