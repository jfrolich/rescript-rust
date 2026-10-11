// Label.disambiguate with no opath warns Ambiguous_name at the label.
type a = {x: int}
type b = {y: int}
type c = {y: int}

let test = (value: int => int) => value.y
