// error-output-parity: Parmatch warns when a GADT catch-all is unused after exhaustive constructor coverage.
@@warning("+11+56-32-34-37")
type rec eq<'a, 'b> = Refl: eq<'a, 'a>

let f: type a. eq<a, int> => int = x =>
  switch x {
  | Refl => 0
  | _ => 1
  }
