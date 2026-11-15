// Signature inclusion pairs the binders of two polymorphic types by
// position, not by name.
module F = (X: {let x: {"f": 'a. 'a => 'a}}): {let x: {"f": 'b. 'b => 'b}} => X

module type A = {let x: {"id": 'a 'b. ([< #A('b)] as 'a) => 'b}}
module G = (X: A): {let x: {"id": 'b 'a. ([< #A('a)] as 'b) => 'a}} => X

module type B = {let x: {"id": 'a 'b. ('a, 'b) => 'a}}
module H = (X: B): {let x: {"id": 'b 'a. ('a, 'b) => 'a}} => X
