// error-output-parity: Typecore.Not_subtype
type a = A | B
type b = C | D

let value = switch C {
| ...a => 0
}
