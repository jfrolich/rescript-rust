type abstractToken = {
  id: int,
  label: string,
}

type publicPosition = [#Top | #Bottom]

type layoutPosition = [#TopRight | #BottomRight | #TopLeft | #BottomLeft | #Top | #Bottom]

type payload<'a> = {
  value: 'a,
  meta: string,
}

type wrapped<'a> =
  | Wrapped(payload<'a>)
  | Missing

let makeToken = id => {id, label: "token-" ++ Int.toString(id)}

let describeToken = token => token.label

let classifyPosition = (position: layoutPosition) =>
  switch position {
  | #TopLeft | #Top => "top-left"
  | #TopRight => "top-right"
  | #BottomLeft => "bottom-left"
  | #BottomRight | #Bottom => "bottom-right"
  }

let widenPosition = (position: publicPosition) => (position :> layoutPosition)

let unwrapInt = wrapped =>
  switch wrapped {
  | Wrapped({value}) => value
  | Missing => 0
  }

module Nested = {
  type t = NestedValue(string)

  let make = value => NestedValue(value)

  let read = item =>
    switch item {
    | NestedValue(value) => value
    }
}

let allValues = (
  describeToken(makeToken(7)),
  classifyPosition(widenPosition(#Bottom)),
  unwrapInt(Wrapped({value: 42, meta: "answer"})),
  Nested.read(Nested.make("nested")),
)
