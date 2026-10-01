// A rebound exception's arguments are its own generalized instance, so a
// pattern binding them gets a fresh copy in each case body.
type t = unknown

exception Error = JsExn

let asJsExn: exn => option<t> = exn =>
  switch exn {
  | Error(t) => Some(t)
  | _ => None
  }

exception Inline({x: int, y: string})
exception Rebound = Inline

let inlineX = exn =>
  switch exn {
  | Rebound({x}) => x
  | Inline(r) => String.length(r.y)
  | _ => 0
  }
