// error-output-parity: Typecore.Exception_pattern_below_toplevel
switch Some(1) {
| Some(exception Not_found) => 0
| _ => 1
}
