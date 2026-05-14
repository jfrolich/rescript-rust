// error-output-parity: Parmatch warns when all match clauses are guarded.
let _ = switch true {
| _ when true => 1
}
