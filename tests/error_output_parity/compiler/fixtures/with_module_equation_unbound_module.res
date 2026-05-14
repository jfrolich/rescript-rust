// error-output-parity: Typetexp.Unbound_module via Pwith_module
module type S = {
  module A: {}
  module B = A
}

module type T = S with module A = Missing
