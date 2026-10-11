// error-output-parity: Typecore.Not_a_variant_type
type r = {x: int}

let value = switch {x: 1} {
| ...r => 0
}
