// Every branch of these matches is partial under its GADT constructor, so
// the match is not exhaustive and keeps its `Match_failure` branch.
@@warning("-8")

type rec t<'a> =
  | Int: t<int>
  | Bool: t<bool>

let bothPartial: type a. (t<a>, a) => int = (x, y) =>
  switch (x, y) {
  | (Int, 1) => 1
  | (Bool, true) => 0
  }

type holder<'a> = {tag: t<'a>, value: 'a}

let record: type a. holder<a> => int = h =>
  switch h {
  | {tag: Int, value: 1} => 1
  | {tag: Bool, value: true} => 0
  }

type rec u<'a> =
  | Int: u<int>
  | Bool: u<bool>
  | Str: u<string>

// `(Bool, Bool, false)` is not matched. Finding it takes the second
// alternative of an or-pattern in Parmatch's counter-example.
let secondAlternative: type a. (u<a>, u<a>, a) => int = (x, y, z) =>
  switch (x, y, z) {
  | (Str, _, _) => 0
  | (_, Bool, true) => 1
  | (_, Int, _) => 2
  }
