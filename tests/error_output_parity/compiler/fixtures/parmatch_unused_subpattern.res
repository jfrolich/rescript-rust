// error-output-parity: Parmatch warns when an or-pattern branch is unused.
let _ = switch true {
| true | true => 1
| false => 2
}
