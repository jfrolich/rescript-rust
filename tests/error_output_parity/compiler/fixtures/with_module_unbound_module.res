// error-output-parity: Typetexp.Unbound_module via Pwith_modsubst
module type S = {
  module A: {}
  module B = A
}

module type T = S with module A := Missing
