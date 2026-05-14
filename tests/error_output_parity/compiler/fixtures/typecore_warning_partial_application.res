// error-output-parity: Typecore emits warning 5 for discarded partial applications.
let _ = {
  let add = (x, y) => x + y
  ignore(add(1, ...))
}
