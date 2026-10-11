// error-output-parity: Typecore.Pattern_type_clash from alias-mediated local GADT constraint attempt
type fn<'a> = 'a => unit
type rec t<'a> = A('a): t<fn<'a>>

let test = (type a, value: t<a>) =>
  switch value {
  | A((inner: a)) => inner
  }
