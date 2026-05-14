// error-output-parity: Typecore.Or_pattern_type_clash
type t = [#A(int) | #B(string)]

let test = (value: t) =>
  switch value {
  | #A(payload) | #B(payload) => payload
  }
