// Opens in signatures and module type shadowing.
module type S = {
  let x: int
}

module M = {
  module type S = {
    let y: int
  }
  type u = int
}

module X: {
  open M
  let z: u
} = {
  let z = 1
}

open M

module Y: S = {
  let y = 1
}
