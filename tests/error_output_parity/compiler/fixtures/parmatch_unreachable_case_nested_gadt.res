// error-output-parity: Parmatch finds unreachable cases whose GADT constructor sits below a record, a constructor argument, an alias, a type argument, a tuple, a polymorphic variant or a locally abstract type.
@@warning("+11+56-32-34-37")
type rec t<'a> =
  | Int: t<int>
  | Bool: t<bool>

type wrap = {tag: t<int>, n: int}
type box = Box(t<int>)
type alias = t<int>
type pair<'a> = ('a, int)
type choice = Left(wrap) | Right(box)

let record = (x: wrap) =>
  switch x {
  | {tag: Int} => 0
  | _ => 1
  }

let single = (x: box) =>
  switch x {
  | Box(Int) => 0
  | _ => 1
  }

let alias = (x: alias) =>
  switch x {
  | Int => 0
  | _ => 1
  }

let argument = (x: option<t<int>>) =>
  switch x {
  | Some(Int) => 0
  | None => 1
  | _ => 2
  }

let tuple = (x: pair<t<int>>) =>
  switch x {
  | (Int, _) => 0
  | _ => 1
  }

let nested = (x: choice) =>
  switch x {
  | Left({tag: Int}) => 0
  | Right(Box(Int)) => 1
  | _ => 2
  }

let variant = (x: [#A(t<int>) | #B]) =>
  switch x {
  | #A(Int) => 0
  | #B => 1
  | _ => 2
  }

type holder<'a> = {kind: t<'a>, value: option<'a>}

let local: type a. (t<a>, option<a>) => int = (x, y) =>
  switch (x, y) {
  | (Int, Some(_)) => 0
  | (Int, _) => 1
  | (Bool, None) => 2
  | (Bool, _) => 3
  | _ => 4
  }

let localRecord: type a. (holder<a>, t<int>) => int = (x, y) =>
  switch (x, y) {
  | ({kind: Int, value: Some(_)}, _) => 0
  | ({kind: Int}, Int) => 1
  | ({kind: Bool}, Int) => 2
  | (_, _) => 3
  }

let refined: type a. (t<a>, a) => int = (x, y) =>
  switch x {
  | Int =>
    switch (y, x) {
    | (0, Int) => 0
    | (_, Int) => 1
    | _ => 2
    }
  | Bool => 3
  }

// No GADT constructor in reach of these.
type plain = {a: option<int>, b: (bool, string)}

let plain = (x: plain) =>
  switch x {
  | {a: Some(1)} => 0
  | {b: (true, _)} => 1
  | {a: None} => 2
  | _ => 3
  }
