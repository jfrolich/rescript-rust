// error-output-parity: Parmatch reads the row of a polymorphic variant pattern in its own pat_env, where the GADT constructor matched before it has refined `a` to the variant; the match env only knows the abstract `a`.
@@warning("+11+56-32-34-37")
type rec t<'a> =
  | Int: t<int>
  | Pv: t<[#A | #B]>

let local: type a. (t<a>, a) => int = (x, y) =>
  switch (x, y) {
  | (Pv, #A) => 0
  | (Pv, #B) => 1
  | (Int, 0) => 2
  | (Int, _) => 3
  }

let partial: type a. (t<a>, a) => int = (x, y) =>
  switch (x, y) {
  | (Pv, #A) => 0
  | (Int, _) => 1
  }
