// error-output-parity: Warning 3 when a deprecated module satisfies a non-deprecated signature.
@@warning("+3-32-34")

module M: {
  module N: {}
} = {
  @deprecated("use O")
  module N = {}
}
