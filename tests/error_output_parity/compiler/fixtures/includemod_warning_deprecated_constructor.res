// error-output-parity: Warning 3 when a deprecated constructor satisfies a non-deprecated signature.
@@warning("+3-32-34")

module M: {
  type t = A
} = {
  type t = | @deprecated("use B") A
}
