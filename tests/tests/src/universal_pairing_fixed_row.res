// A variant row whose row variable is universal is fixed: unification
// cannot drop its constructors.
type a = {"f": 'a 'r. ([< #A('a) | #B] as 'r) => 'a}
type b = {"f": 'b 's. ([< #A('b) | #B] as 's) => 'b}
let f = (x: a): b => x

let g = (x: [< #A(int)]) => (x: [< #A(int) | #B])
