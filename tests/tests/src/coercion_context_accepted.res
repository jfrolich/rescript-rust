// Coercions that succeed, each standing in a context that reports its own
// clash: comparison, array item, if return, function argument, record field.

type t = private int

type r = {a: int}

let same = (x: int, y: int) => x == y

let compared = (x: t) => 1 === (x :> int)

let items = (v: [#A]) => [#B, (v :> [#A | #B])]

let branch = (b, x: t) => if b { 1 } else { (x :> int) }

let argument = (x: t) => same(1, (x :> int))

let field = (x: t) => {a: (x :> int)}

let narrowed = (o: {"a": int, "b": int}) => [(o :> {"a": int}), {"a": 2}]
