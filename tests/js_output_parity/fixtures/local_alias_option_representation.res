module ST = {
  type t = Bug | Feedback
}
type state = {initialType: ST.t}
module Cfg = {
  type t = ST.t
  let label = (t: t) => switch t { | Bug => "Bug" | Feedback => "F" }
}
let f = (~x=?, ()) => switch x { | Some(s) => Cfg.label(s) | None => "" }
let g = (state: state) => f(~x=state.initialType, ())
type props<'a> = {x?: 'a}
let h = ({?x}: props<_>) => switch x { | Some(s) => Cfg.label(s) | None => "" }
let i = (state: state) => h({x: state.initialType})
