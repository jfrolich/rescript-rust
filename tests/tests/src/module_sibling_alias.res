// Sibling module aliases read from another unit: `module Aliased = One`
// keeps the raw alias target in the unit's signature.
module One = {
  let make = () => 1
  let value = 2
  type t = A | B
}
module Aliased = One
module Chained = Aliased

module Two = {
  // Shadows the top-level One inside Two.
  module One = {
    let make = () => 10
    let value = 20
  }
  module Inner = One
  module Outer = Aliased
}

module Three = {
  module Deep = {
    module One = {
      let make = () => 100
    }
    module Local = One
  }
  module Up = Deep.Local
}
