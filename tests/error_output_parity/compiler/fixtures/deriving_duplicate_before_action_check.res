// process_derive_type reports a second @deriving before any action is checked.
@deriving(t) @deriving(jsConverter)
type t = One | Two
