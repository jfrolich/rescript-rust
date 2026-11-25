// A deprecated codec is used by both encoder bindings: two warnings.
module M = {
  type t = int

  @deprecated("Use another codec")
  let t_encodeJson = Spice.intToJson

  let t_decode = Spice.intFromJson
}

@spice
type t = array<M.t>
