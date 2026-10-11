// error-output-parity: Typecore.Field_not_optional
type r = {nonopt: int, opt?: string}

let f = r =>
  switch r {
  | {nonopt: ?_, opt: ?_} => true
  }
