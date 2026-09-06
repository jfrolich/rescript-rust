module First = {
  type t = {value: int}
  type rec chain = End | Next(int, chain)
  let identity = (x: t) => x
}
module Alias = First
module Captured = {
  module Before = Alias
  module Alias = {type t = {value: string}}
  let old: Before.t = {value: 7}
  let fresh: Alias.t = {value: "seven"}
}
let a: First.t = {value: 3}
let b: Alias.t = Alias.identity(a)
let tree: First.chain = Next(4, End)
let result = (a.value, b.value, Captured.old.value, Captured.fresh.value, tree)
