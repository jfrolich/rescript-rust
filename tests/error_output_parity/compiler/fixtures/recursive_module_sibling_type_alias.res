// error-output-parity: recursive-module inclusion must use OCaml's
// check_recmodule_inclusion unrolling, so this accepted program must not
// produce a Rust-only signature mismatch for B.t.
module rec A: {
  type t = B.t
} = {
  type t = int
}
and B: {
  type t
} = {
  type t = int
}
