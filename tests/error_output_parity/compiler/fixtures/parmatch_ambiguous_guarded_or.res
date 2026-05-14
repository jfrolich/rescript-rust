// error-output-parity: Parmatch warns for ambiguous guarded or-pattern variables.
let _ = switch (Some(1), Some(2)) {
| (Some(x), _) | (_, Some(x)) when x > 0 => 1
| _ => 0
}
