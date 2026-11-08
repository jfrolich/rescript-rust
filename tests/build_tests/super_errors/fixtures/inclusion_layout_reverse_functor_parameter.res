module M: {
  module type T = {
    module G: (Y: {let a: int; let b: int}) => {}
  }
} = {
  module type T = {
    module G: (Y: {let a: int}) => {}
  }
}
