// An inline record of an extension constructor of an opened module.

module R = {
  exception E({v: int, w: string})
  type t = ..
  type t += C({v: int})
  type u = A({x: int})
}

open R

let e = E({v: 1, w: "a"})
let c = C({v: 2})
let a = A({x: 3})

let f = x =>
  switch x {
  | E({v, w}) => v + String.length(w)
  | _ => 0
  }

let g = (x: t) =>
  switch x {
  | C({v}) => v
  | _ => 0
  }

let local = {
  open Inline_record_extension_lib
  E({v: 4})
}

let h = x => {
  open! Inline_record_extension_lib
  switch x {
  | C({v}) => v
  | _ => 0
  }
}
