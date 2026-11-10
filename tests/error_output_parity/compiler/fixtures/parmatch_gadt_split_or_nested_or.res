// error-output-parity: splitting a counter-example's or-pattern on its GADT constructors splits that or-pattern only: the subpatterns of the alternative taken are typed in `Normal` mode (typecore.ml:1257), so the reported example keeps its nested `B | C`.
type rec t<'a> =
  | Int: t<int>
  | Bool: t<bool>

type abc = A | B | C

let after: type a. (t<a>, a, abc) => int = (x, y, z) =>
  switch (x, y, z) {
  | (Int, 1, A) => 1
  | (Bool, true, A) => 2
  }

let single: type a. (t<a>, a, abc) => int = (x, y, z) =>
  switch (x, y, z) {
  | (Int, 1, A) => 1
  }
