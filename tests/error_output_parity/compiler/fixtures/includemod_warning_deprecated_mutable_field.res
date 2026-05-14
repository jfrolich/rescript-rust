// error-output-parity: Warning 3 when a deprecated-mutable field satisfies a non-deprecated signature.
@@warning("+3-32-34")

module M: {
  type t = {
    mutable x: int,
  }
} = {
  type t = {
    @deprecated_mutable("use setX")
    mutable x: int,
  }
}
