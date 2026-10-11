// error-output-parity: Parmatch warns when a match case is fully unused.
let _ = switch true {
| true => 1
| true => 2
| false => 3
}
