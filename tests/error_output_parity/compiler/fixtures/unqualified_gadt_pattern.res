// error-output-parity: Typecore.Unqualified_gadt_pattern
module M = {
  type rec t<'a> = A: t<int>
}

let test = (value: M.t<int>) =>
  switch value {
  | A => 1
  }
