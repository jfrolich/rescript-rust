// Local `open` of a functor is Structure_expected.
module type S = {}
module F = (X: S) => {}
let f = () => {
  open F
  1
}
