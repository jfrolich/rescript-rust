// Pexp_record: `ty_record` is a fresh variable when the expected type is not
// a concrete record; it is unified with the expected type after the labels.
type point = {x: int, y: int}

let p = {x: 1, y: 2}
let () = p.x = {x: 1, y: 2}
