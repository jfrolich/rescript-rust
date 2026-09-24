@ocaml.unboxed type r = {x: int}
@ocaml.unboxed type v = A(int)
let f = (r: r, v: v) => (r.x, v)
@ocaml.boxed @unboxed type w = int
