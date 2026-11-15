// The unit holds polymorphic types, so its inferred signature is checked:
// each accepted here as OCaml accepts it.
let apply = (x: {"f": 'a. [< #A('a)] => int}) => x["f"](#A(1))
let id = (x: {"f": 'a. 'a => 'a}) => x
type r = {g: 'a. array<'a> => int}
let len = {g: a => Array.length(a)}
let both = (x: {"f": 'a. 'a => 'a}) => (x["f"](1), x["f"]("s"))
let pair = (x: {"f": 'a. [< #A('a) | #B] => int}, y: [< #A(int) | #B]) => x["f"](y)
