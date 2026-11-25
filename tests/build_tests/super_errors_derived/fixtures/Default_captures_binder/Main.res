// A user expression is typed among the binders of the generated decoder:
// `v` here is the decoder's parameter, a `JSON.t`, not the `v` above.
let v = 2

@spice
type t = {@spice.default(v) b: int}
