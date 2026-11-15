module R = {
  module type Sig = {
    let x: int
  }
}
module M: R.Sigg = {
  let x = 1
}
