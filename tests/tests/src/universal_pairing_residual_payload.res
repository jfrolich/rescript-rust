// A payload that holds no universal variable stays in the conjunction of a
// residual row field.
let g = (y: [< #A(int)], h: {"f": 'a. ([< #A('a)] as 'r) => 'a}) => h["f"](y)

let k = (y: [< #A(int) | #B], z: [< #A(int)]) => (y, (z :> [< #A(int) | #B]))
