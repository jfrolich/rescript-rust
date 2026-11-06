let aliased = Module_sibling_alias.Aliased.make()
let aliasedValue = Module_sibling_alias.Aliased.value
let chained = Module_sibling_alias.Chained.make()
let ctor: Module_sibling_alias.Aliased.t = Module_sibling_alias.Aliased.A

let inner = Module_sibling_alias.Two.Inner.make()
let innerValue = Module_sibling_alias.Two.Inner.value
let outer = Module_sibling_alias.Two.Outer.make()

let deep = Module_sibling_alias.Three.Deep.Local.make()
let up = Module_sibling_alias.Three.Up.make()

module P = Module_sibling_alias
let viaLocal = P.Two.Inner.make() + P.Aliased.make()

module One = {
  let make = () => 1000
}
let localOne = One.make()
let unitOne = Module_sibling_alias.One.make()

let z = 3
module Probe = (I: {}) => {}
