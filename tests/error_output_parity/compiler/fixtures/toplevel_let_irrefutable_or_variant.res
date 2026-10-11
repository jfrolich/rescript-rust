// Or-patterns and closed variants can be irrefutable.
type t = A | B
let (A | B) = A
let #a = #a
