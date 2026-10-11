type t = {a: int, b: int}
let @val {a, ...t as rest} = ({a: 1, b: 2}: t)
let {a, ...t as rest2} = ({a: 1, b: 2}: t)
