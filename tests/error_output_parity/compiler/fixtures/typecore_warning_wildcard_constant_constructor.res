// error-output-parity: Typecore emits warning 28 for wildcard payloads on constant constructors.
let value = switch None {
| None(_) => 0
| Some(_) => 1
}
