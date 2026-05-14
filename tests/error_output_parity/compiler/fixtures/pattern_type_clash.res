// error-output-parity: Typecore.Pattern_type_clash
let value = switch 1 {
| "x" => 0
| _ => 1
}
