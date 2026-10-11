// error-output-parity: Warning 3 when a deprecated value satisfies a non-deprecated signature.
@@warning("+3-32-34")

module M: {
  external x: int => int = "%identity"
} = {
  @deprecated("use y")
  external x: int => int = "%identity"
}
