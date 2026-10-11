// error-output-parity: Typetexp.Ill_typed_functor_application
module F = (_X: {}) => {}
module A = {}
type t = F(A).t
