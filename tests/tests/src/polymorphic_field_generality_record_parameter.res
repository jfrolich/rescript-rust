type t<'a> = {f: 'b. 'b => 'a}

let constant = {f: _ => 1}

let make = (x: 'a): t<'a> => {f: _ => x}

let applied = make("x").f(3)

let matched = switch constant {
| {f} => f(2)
}
