// `@spice.codec` takes an (encoder, decoder) pair; these are no functions.
let bad = (1, 2)

@spice
type t = {field: @spice.codec(bad) string}
