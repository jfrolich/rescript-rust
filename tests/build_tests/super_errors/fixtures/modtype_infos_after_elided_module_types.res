// The outer module types are big and elided; the module type declarations
// and the inner module types after them are small and printed.
module M: {
  module type S = {
    let x0: int
    let x1: int
    let x2: int
    let v: string
  }
} = {
  module type S = {
    let x0: int
    let x1: int
    let x2: int
    let v: int
  }
}
