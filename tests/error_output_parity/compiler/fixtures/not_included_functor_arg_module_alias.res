// error-output-parity: Includemod functor-body module alias requirement
module F: (X: {}) => {
  module Y = X
} = (X: {}) => {
  module Y = X
}
