// A codec reached through an `open` uses that open; `Unrelated` stays unused.
module Codecs = {
  type id = string
  let id_encodeJson = Spice.stringToJson
  let id_decode = Spice.stringFromJson
}

module Unrelated = {
  let unused = 1
}

open Codecs
open Unrelated

@spice
type ids = array<id>
