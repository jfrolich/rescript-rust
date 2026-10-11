// error-output-parity: Typemod.Scoping_pack for packaged structure local type constraints.

module type S = {
  type t
}

let f = (packed: module(S with type t = 'a)) => packed

let value = f(module({
  type t
})
)
