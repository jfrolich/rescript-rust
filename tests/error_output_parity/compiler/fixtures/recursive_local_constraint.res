// error-output-parity: Typecore.Pattern_type_clash local GADT constraint
type rec t<'a> = A(t<'a>): t<array<'a>>

let test = (type a, value: t<a>) =>
  switch value {
  | A((inner: t<a>)) => inner
  }
