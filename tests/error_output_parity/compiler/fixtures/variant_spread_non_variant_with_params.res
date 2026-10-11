// A spread of a non-variant type is InvalidType even when it has parameters.
type a<'x> = array<'x>

type b =
  | ...a<int>
  | C
