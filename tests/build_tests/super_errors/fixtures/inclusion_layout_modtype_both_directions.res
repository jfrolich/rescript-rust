module M: {
  module type T = {
    let a: int
    let c: int
  }
} = {
  module type T = {
    let a: int
    let b: int
  }
}
