// error-output-parity: Typecore.Incoherent_label_order
let test = f => {
  let _ = f(~a=1, ~b=2)
  f(~b=2, ~a=1)
}
