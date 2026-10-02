// Pexp_setfield returns through `rue`, so the clash is reported as
// "This has type: unit" against the expected type.
type r = {mutable x: int}
let r = {x: 1}
let (2, 4) = r.x = 2
