// The unused check of a locally abstract type is a delayed check: it is not
// printed when a later error stops typing.
let x: type t. (int, int) => int = (a, b) => a + b

let y: type t u. (t, u) => t = (x, _: {..}) => x
