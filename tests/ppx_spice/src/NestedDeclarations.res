// Declarations that derive codecs inside a module expression: a submodule,
// a submodule of a submodule, a functor body, a first-class module, a module
// bound in an expression and the right-hand side of a recursive binding
// (`%%private` admits no type declaration). Records too, so every nested shape is covered whichever
// shapes take a plan.
module Plain = {
  @spice
  type id = string

  @spice
  type ids = array<id>

  @spice
  type point = {x: int, y: option<float>, label?: string}

  module Deeper = {
    @spice
    type maybeIds = option<ids>

    @spice
    type line = {from: point, to_: point}
  }
}

module type Codec = {
  type t
  let t_encode: t => JSON.t
  let t_encodeJson: t => JSON.t
  let t_decode: JSON.t => result<t, Spice.decodeError>
}

module Many = (Item: Codec) => {
  @spice
  type items = array<Item.t>

  @spice
  type page = {items: items, next: option<string>}
}

module Ids = Many({
  @spice
  type t = string
})

module type Named = {
  type name
  let name_encode: name => JSON.t
  let name_decode: JSON.t => result<name, Spice.decodeError>
}

let named: module(Named) = module(
  {
    @spice
    type name = string
  }
)

let localEncode = {
  module Local = {
    @spice
    type flags = array<bool>

    @spice
    type options = {flags: flags, verbose: bool}
  }
  (flags, verbose) => Local.options_encode({flags, verbose})
}

let rec encodeDepth = (depth: int): JSON.t => {
  module Step = {
    @spice
    type depths = array<int>
  }
  let depths: Step.depths = [depth]
  depth <= 0 ? Step.depths_encode(depths) : encodeDepth(depth - 1)
}

let roundTrip = (line: Plain.Deeper.line) => Plain.Deeper.line_decode(Plain.Deeper.line_encode(line))
let page = (page: Ids.page) => Ids.page_decode(Ids.page_encode(page))
