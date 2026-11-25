// A nested decoder sees the enclosing local result-constructor name.
type mine = Ok(int) | Bad
module Nested = {
  @spice type t = {value: int}
}
