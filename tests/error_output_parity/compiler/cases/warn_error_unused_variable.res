// error-output-parity: -warn-error +A promotes warning 26 to a fatal diagnostic.
let f = x => {
  let unused = x
  1
}
