// A copied polymorphic type keeps a row binder that is also the tail of a
// variant row in its body.
type a = {"f": 'a 'r. ([< #A('a)] as 'r) => 'a}
let f = (x: a): {"f": 'a 'r. ([< #A('a)] as 'r) => 'a} => x

module type A = {let x: {"id": 'a. ([< #A | #B] as 'a) => 'a}}
module F = (X: A): {let x: {"id": 'a. ([< #A | #B] as 'a) => 'a}} => X
