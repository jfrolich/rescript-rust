// Type equality pairs the binders of two polymorphic fields by position,
// not by name.
type t = {f: 'b. 'b => 'b}
type u = {g: 'b 'a. ('a, 'b) => 'a}
