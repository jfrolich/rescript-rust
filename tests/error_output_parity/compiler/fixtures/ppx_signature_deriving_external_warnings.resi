@deriving(accessors)
type t
external f: @string [#a] => unit = "f"
let x: int
