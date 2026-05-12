// error-output-parity: Typetexp.Unbound_modtype inside signature item
module type S = {
  module type T = Missing
}

module N: S = {
  module type T = {}
}
