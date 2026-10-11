// Recover.default_type carries no attributes: no unused-attribute warnings.
external f: @string @int #A[ | #B] => unit = "f"

let _ = f(#A)
