// error-output-parity: string interpolation is rejected in patterns.
switch value {
| `prefix ${part}` => ()
| _ => ()
}
