// error-output-parity: Typecore.type_construct reports Typetexp.Unbound_constructor
// at the constructor longident location, not the whole constructor expression.
module M = {
  let value = 1
}

module N = {}

let value = M(N).value
