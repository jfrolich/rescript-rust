// error-output-parity: when the alternative taken for a split or-pattern of a counter-example makes a later part of the pattern ill-typed, OCaml goes back and takes the other alternative (typecore.ml:1713-1720). These matches are not exhaustive only through such a second alternative; without it they pass as exhaustive and a case is reported as unreachable.
type rec t<'a> =
  | Int: t<int>
  | Bool: t<bool>
  | Str: t<string>

let secondAlternative: type a. (t<a>, t<a>, a) => int = (x, y, z) =>
  switch (x, y, z) {
  | (Str, _, _) => 0
  | (_, Bool, true) => 1
  | (_, Int, _) => 2
  }

let twoSplits: type a b. (t<a>, t<b>, t<a>, t<b>, a, b) => int = (x1, x2, y1, y2, v1, v2) =>
  switch (x1, x2, y1, y2, v1, v2) {
  | (Str, _, _, _, _, _) => 0
  | (_, Str, _, _, _, _) => 0
  | (_, _, Bool, Bool, true, true) => 1
  | (_, _, Int, _, _, _) => 2
  | (_, _, _, Int, _, _) => 2
  }
