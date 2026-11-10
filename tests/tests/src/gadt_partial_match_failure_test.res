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
