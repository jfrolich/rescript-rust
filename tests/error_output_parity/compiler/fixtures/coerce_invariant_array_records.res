// Ctype.subtype: an invariant type argument is checked both ways and, when
// that fails, unified as a deferred constraint; the report prints both traces.
type r1 = {x: int}
type r2 = {}

type t1 = array<r1>
type t2 = array<r2>

let foo = (x: t1) => {(x :> t2)}
