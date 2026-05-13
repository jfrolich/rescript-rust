// error-output-parity: Typetexp.Illegal_reference_to_recursive_module
module rec A: {
  module B: module type of A
} = {
  module B = A
}
