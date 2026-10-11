// error-output-parity: Includemod functor-body module alias mismatch formatting
module A = {}
module F: (X: {}) => {
  module Y = X
} = (X: {}) => {
  module Y = A
}
