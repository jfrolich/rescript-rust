// A record pattern binds each label once.
type t = {a: int, b: int}
let f = ({a: x, a: y}: t) => x + y
