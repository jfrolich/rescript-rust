module M: {
  module F: (
    X: {
      module type T = {
        module G: (Y: {let a: int; let b: int}) => {}
      }
    },
  ) => {}
} = {
  module F = (
    X: {
      module type T = {
        module G: (Y: {let a: int}) => {}
      }
    },
  ) => {}
}
