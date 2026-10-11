type item = {
  name: string,
  count: int,
}

type code = [#Primary | #Secondary | #Danger]

type payload = {
  name: string,
  count: int,
  tag: string,
}

let make: (~name: string, ~count: int=?) => item = (~name, ~count=1) => {name, count}

let label: item => string = item => item.name ++ ":" ++ Int.toString(item.count)

let classify = code =>
  switch code {
  | #Primary => "primary"
  | #Secondary => "secondary"
  | #Danger => "danger"
  }

let fromPayload = payload => make(~name=payload.name ++ "-" ++ payload.tag, ~count=payload.count)

let exportedTuple = (make(~name="root", ~count=2), classify(#Primary))

module Nested = {
  type t = NestedValue(int)

  let make = value => NestedValue(value + 1)

  let value = item =>
    switch item {
    | NestedValue(value) => value
    }
}
