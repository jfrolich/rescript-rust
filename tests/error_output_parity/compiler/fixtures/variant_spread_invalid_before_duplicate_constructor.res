// Variant spreads are expanded and validated before transl_declaration checks
// for duplicate constructors.
type a = int

type b =
  | ...a
  | C
  | C
