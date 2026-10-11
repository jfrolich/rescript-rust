// error-output-parity: pattern tuples require at least two elements.
switch value {
| (item, ) => ()
| _ => ()
}
