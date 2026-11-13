// The custom codec encodes and decodes `int`; the field is a `string`.
let intCodec = (Spice.intToJson, Spice.intFromJson)

@spice
type t = {field: @spice.codec(intCodec) string}
