// error-output-parity: @@warnerror uses Warnings.parse_options true semantics.
@@warnerror("+A")

let f = x => {
  let unused = x
  1
}
