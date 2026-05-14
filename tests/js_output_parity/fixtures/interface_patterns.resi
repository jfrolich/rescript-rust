type abstractToken

type publicPosition = [#Top | #Bottom]

type layoutPosition = [#TopRight | #BottomRight | #TopLeft | #BottomLeft | #Top | #Bottom]

type payload<'a> = {
  value: 'a,
  meta: string,
}

type wrapped<'a> =
  | Wrapped(payload<'a>)
  | Missing

let makeToken: int => abstractToken

let describeToken: abstractToken => string

let widenPosition: publicPosition => layoutPosition

let unwrapInt: wrapped<int> => int

module Nested: {
  type t
  let make: string => t
  let read: t => string
}

let allValues: (string, string, int, string)
