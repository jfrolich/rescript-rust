// error-output-parity: module rec in a signature binds its modules for later items.
module type S = {
  module rec A: {
    type t
    let x: B.t
  }
  and B: {
    type t = A.t
  }
}
module F = (X: S) => {
  let y: string = X.A.x
}
