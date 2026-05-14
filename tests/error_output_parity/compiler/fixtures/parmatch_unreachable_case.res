// error-output-parity: Parmatch warns when a GADT-indexed catch-all is unreachable.
@@warning("+56-32-34-37")
type rec t<'a> =
  | Int: t<int>
  | Bool: t<bool>

let f = (x: t<int>) =>
  switch x {
  | Int => 0
  | _ => 1
  }
