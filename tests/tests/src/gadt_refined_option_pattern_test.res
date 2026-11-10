// A GADT constructor matched earlier in the same pattern refines `a`, so
// `Some(0)` matches an `option<int>`: the payload cannot be a nested
// option and is read without `Primitive_option.valFromOption`.
type rec t<'a> =
  | Int: t<int>
  | Bool: t<bool>

let local: type a. (t<a>, option<a>) => int = (x, y) =>
  switch (x, y) {
  | (Int, Some(0)) => 0
  | (Int, _) => 1
  | (Bool, None) => 2
  | (Bool, _) => 3
  }

type holder<'a> = {tag: t<'a>, value: option<'a>}

let field: type a. holder<a> => int = h =>
  switch h {
  | {tag: Int, value: Some(0)} => 0
  | {tag: Int, _} => 1
  | {tag: Bool, value: Some(true)} => 2
  | {tag: Bool, _} => 3
  }

// The binder is typed before the constructor that refines `a`; it still gets
// the equation, as every pattern node gets the env of the whole pattern.
let bindsFirst: type a. (option<a>, t<a>) => int = (y, x) =>
  switch (y, x) {
  | (Some(v), Int) => v + 1
  | (_, Int) => 1
  | (_, Bool) => 3
  }
