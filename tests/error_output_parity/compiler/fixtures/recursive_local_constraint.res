// error-output-parity: Typecore.Recursive_local_constraint local GADT constraint
type rec t<'a> = A(t<'a>): t<array<'a>>

let test = (type a, value: t<a>) =>
  switch value {
  | A((inner: t<a>)) => inner
  }
