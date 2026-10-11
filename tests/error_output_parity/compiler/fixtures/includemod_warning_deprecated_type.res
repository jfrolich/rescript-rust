// error-output-parity: Warning 3 when a deprecated type satisfies a non-deprecated signature.
@@warning("+3-32-34")

module M: {
  type t = int
} = {
  @deprecated("use u")
  type t = int
}
