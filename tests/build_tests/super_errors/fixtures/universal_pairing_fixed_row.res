type a = {"f": 'a 'r. ([< #A('a)] as 'r) => 'a}
type b = {"f": 'b 'r. ([< #A('b) | #B] as 'r) => 'b}
let f = (x: a): b => x
