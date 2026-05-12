// error-output-parity: Typetexp.Access_functor_as_structure
module type S = {
  let value: int
}

module F = (X: S) => {
  let value = X.value
}

let value = F.value
