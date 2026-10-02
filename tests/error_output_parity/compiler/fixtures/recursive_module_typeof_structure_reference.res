// error-output-parity: module type of structure inside recursive module approximation
module rec A: module type of {
  module B = A
} = A
