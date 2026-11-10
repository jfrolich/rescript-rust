// error-output-parity: Parmatch.do_check_fragile reads a sibling's type in its own pat_env, where the GADT constructor matched before it has refined `a`: `true` is a bool, which is not extendable, so only `t` is reported, and only when a wildcard covers its constructors.
@@warning("+11+56-32-34-37")
type rec t<'a> =
  | Int: t<int>
  | Bool: t<bool>

let local: type a. (t<a>, a) => int = (x, y) =>
  switch (x, y) {
  | (Int, 0) => 0
  | (Int, _) => 1
  | (Bool, true) => 2
  | (Bool, _) => 3
  }

let trailing: type a. (t<a>, a) => int = (x, y) =>
  switch (x, y) {
  | (Int, 0) => 0
  | (Int, _) => 1
  | (Bool, true) => 2
  | (Bool, _) => 3
  | _ => 4
  }

type holder<'a> = {tag: t<'a>, value: 'a}

let record: type a. holder<a> => int = h =>
  switch h {
  | {tag: Int, value: 0} => 0
  | {tag: Int, _} => 1
  | {tag: Bool, value: true} => 2
  | {tag: Bool, _} => 3
  | _ => 4
  }
