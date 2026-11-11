open Macro

// The type of a parameter says when it exists. `base` is code<float>: the
// macro gets the code of the argument. `n` is an int: the macro gets the
// number, so the call has to pass a literal.
@generic
let rec pow = (base: code<float>, n: int): code<float> =>
  if n == 0 {
    %code(1.0)
  } else if mod(n, 2) == 0 {
    %code({
      let half = ${pow(base, n / 2)}
      half *. half
    })
  } else {
    %code(${base} *. ${pow(base, n - 1)})
  }
