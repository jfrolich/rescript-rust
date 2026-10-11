// error-output-parity: Typecore.Invalid_interval
let value = switch 2 {
| 1 .. 3 => true
| _ => false
}
