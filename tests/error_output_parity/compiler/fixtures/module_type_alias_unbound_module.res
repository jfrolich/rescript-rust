// error-output-parity: Typetexp.Unbound_module via Typemod.Pmty_alias
module type S = {
  module M = Missing
}

module N: S = {
  module M = {}
}
