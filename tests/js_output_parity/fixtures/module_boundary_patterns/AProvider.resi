type item

type code = [#Primary | #Secondary | #Danger]

type payload = {
  name: string,
  count: int,
  tag: string,
}

let make: (~name: string, ~count: int=?) => item

let label: item => string

let classify: code => string

let fromPayload: payload => item

let exportedTuple: (item, string)

module Nested: {
  type t
  let make: int => t
  let value: t => int
}
