// error-output-parity: Parmatch warns when a catch-all keeps a variant match exhaustive after future constructors.
@@warning("-32-34-37")

type t = A | B

let _f = x =>
  switch x {
  | A => 1
  | _ => 2
  }
