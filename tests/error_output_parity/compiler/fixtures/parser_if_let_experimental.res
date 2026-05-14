// error-output-parity: if-let emits the experimental parser diagnostic.
let _ = if let Some(value) = result {
  value
}
