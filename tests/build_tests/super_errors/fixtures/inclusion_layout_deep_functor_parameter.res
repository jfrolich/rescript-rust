module M: {
  module F: (X: (Y: (Z: {let a: int}) => {}) => {}) => {}
} = {
  module F = (X: (Y: (Z: {let a: string}) => {}) => {}) => {}
}
