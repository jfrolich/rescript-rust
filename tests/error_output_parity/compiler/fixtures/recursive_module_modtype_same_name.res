module type S = {
  module M: {
    let f: unit => unit
  }
}
module Make = (X: {}) => {
  module M = {
    let f = () => ()
  }
}
module rec A: {} = {}
and S: S = {
  module C = Make(A)
  include C
}
