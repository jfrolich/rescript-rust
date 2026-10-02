// Constructor.disambiguate with an expected type path: a qualified
// constructor of another type is a Name_type_mismatch.
module M = {
  type t = Wrap(int)
}

let f = (x: unit) =>
  switch x {
  | M.Wrap(_) => 1
  }
