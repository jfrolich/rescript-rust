// A type variable of a polymorphic method may be instantiated with a type
// that holds no universal variable of the method.
module type A = {let x: {"f": 'b. 'b => 'a}}
module F = (X: A): {let x: {"f": 'b. 'b => int}} => X
