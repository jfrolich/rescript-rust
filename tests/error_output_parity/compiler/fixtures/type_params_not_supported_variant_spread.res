// error-output-parity: Typecore.Type_params_not_supported
type t<'a> = A('a) | B

let value = switch B {
| ...t => 0
}
