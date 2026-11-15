module type A = {let x: {"id": 'a 'b. ('a, 'b) => 'a}}
module F = (X: A): {let x: {"id": 'a 'b. ('a, 'b) => 'b}} => X
