module N = {let x = 1}
module F = (X: {
  module N: {let x: int}
  module M = N
}): {module Z: {let x: string}} => {module Z = X.M}
