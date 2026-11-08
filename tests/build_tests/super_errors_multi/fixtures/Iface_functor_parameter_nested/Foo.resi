module F: (
  X: {
    module type T = {
      module G: (Y: {let a: int}) => {let r: int}
    }
  },
) => {}
