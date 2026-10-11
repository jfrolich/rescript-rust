// error-output-parity: Typecore emits warning 52 for literal payload exception patterns.
let value = try {
  raise(Failure("boom"))
} catch {
| Failure("boom") => 1
| _ => 0
}
