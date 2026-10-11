// error-output-parity: Warning 3 when a deprecated module type satisfies a non-deprecated signature.
@@warning("+3-32-34")

module M: {
  module type S = {}
} = {
  @deprecated("use T")
  module type S = {}
}
