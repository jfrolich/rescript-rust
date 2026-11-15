// An inline record of an extension constructor, built and matched through a
// module path: the record is typed against the constructor's own record type.

module R = {
  exception E({v: int})
  type t = ..
  type t += C({v: int})
  type u = A({w: int})
  let inside = E({v: 0})
}

module Outer = {
  module S = {
    exception E({v: int, w?: string})
  }
}

let e = R.E({v: 1})
let c = R.C({v: 2})
let a = R.A({w: 3})

let v = 4
let punned = R.E({v: v})
let deep = Outer.S.E({v: 5})
let withOptional = Outer.S.E({v: 6, w: "x"})
let withOptionalOption = Outer.S.E({v: 7, w: ?Some("y")})

exception E({w: string})
let shadowed = E({w: "z"})

let exnField = x =>
  switch x {
  | R.E({v}) => v
  | Outer.S.E({v, ?w}) =>
    switch w {
    | Some(w) => v + String.length(w)
    | None => v
    }
  | _ => 0
  }

let extField = (x: R.t) =>
  switch x {
  | R.C({v}) => v
  | _ => 0
  }

let recordAccess = x =>
  switch x {
  | R.E(r) => r.v
  | _ => 0
  }

let update = x =>
  switch x {
  | Outer.S.E(r) => throw(Outer.S.E({...r, v: 8}))
  | _ => ()
  }
