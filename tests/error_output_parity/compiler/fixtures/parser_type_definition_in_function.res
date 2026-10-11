// error-output-parity: type declarations are rejected inside function bodies.
let f = () => {
  type t = int
}
