// The default of an `int` field is a string.
@spice
type t = {@spice.default("x") count: int}
