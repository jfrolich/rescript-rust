module Spice = {
  type decodeError = {path: string, message: string, value: int}
}
let f = (t): result<int, Spice.decodeError> =>
  Error({
    open Spice
    {path: "a", message: "b", value: t}
  })
module Other = {
  type state = Idle | Thinking(string) | Generating
  let make = () => Thinking("x")
}
type state = Other.state = Idle | Thinking(string) | Generating
let g = (s: state) => switch s {
| Idle => 1
| Thinking(_) | Generating => 2
}
