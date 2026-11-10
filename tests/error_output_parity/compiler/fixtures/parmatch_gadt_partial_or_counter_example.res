// error-output-parity: Parmatch's counter-example `(Int, 0) | (Bool, false)` is typed again with its or-pattern split on the GADT constructors (typecore.ml:1444-1445, 1713-1721), so each alternative refines `a` on its own and the match is reported as not exhaustive.
type rec t<'a> =
  | Int: t<int>
  | Bool: t<bool>

let bothPartial: type a. (t<a>, a) => int = (x, y) =>
  switch (x, y) {
  | (Int, 1) => 1
  | (Bool, true) => 0
  }

let firstPartial: type a. (t<a>, a) => int = (x, y) =>
  switch (x, y) {
  | (Bool, true) => 0
  | (Int, 1) => 1
  }

type holder<'a> = {tag: t<'a>, value: 'a}

let record: type a. holder<a> => int = h =>
  switch h {
  | {tag: Int, value: 1} => 1
  | {tag: Bool, value: true} => 0
  }
