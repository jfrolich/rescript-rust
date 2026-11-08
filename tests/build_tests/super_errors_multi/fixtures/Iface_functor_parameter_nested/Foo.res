module F = (
  X: {
    module type T = {
      module G: (Y: {let a: string}) => {let r: int}
    }
  },
) => {}
