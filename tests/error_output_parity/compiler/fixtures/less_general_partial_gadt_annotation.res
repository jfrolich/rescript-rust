// error-output-parity: Less_general names the free variable before the universal one.
@@warning("+11+56-32-34-37")
type rec eq<'a, 'b> = Refl: eq<'a, 'a>

let f: type a. eq<a, _> => int = x =>
  switch x {
  | Refl => 0
  | _ => 1
  }
