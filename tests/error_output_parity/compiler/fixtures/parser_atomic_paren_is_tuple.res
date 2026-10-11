// After recovering from `->`, `(t, _)` is an atomic tuple type, not a parameter list.
type t
@set external clearNodeValue: -> (t, @as(json`null`) _) => unit = "nodeValue"
