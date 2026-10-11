type stringCode = | @as("red") Red | @as("blue") Blue
type intCode = | @as(1) Low | @as(2) High
type floatCode = | @as(1.5) Cold | @as(2.5) Hot
type bigintCode = | @as(1n) Small | @as(2n) Large

let coercedValues = (
  (Red :> string),
  (High :> int),
  (Hot :> float),
  (Large :> bigint),
)

@unboxed
type jsonish =
  | @as(false) JsonFalse
  | @as(true) JsonTrue
  | @as(null) JsonNull
  | @as(undefined) JsonUndefined
  | JsonString(string)
  | JsonNumber(float)
  | JsonArray(array<int>)
  | JsonObject({name: string, count?: int})

let classifyJsonish = value =>
  switch value {
  | JsonFalse => "false"
  | JsonTrue => "true"
  | JsonNull => "null"
  | JsonUndefined => "undefined"
  | JsonString(text) => text
  | JsonNumber(number) => Float.toString(number)
  | JsonArray(values) => Int.toString(Array.length(values))
  | JsonObject({name, count}) => name ++ Int.toString(count)
  | JsonObject({name}) => name
  }

@unboxed
type nullableInt = | @as(null) EmptyNull | PresentInt(int)

@unboxed
type maybeName = | @as(undefined) MissingName | PresentName(string)

let mergeNullish = (left, right) => {
  let fromLeft =
    switch left {
    | EmptyNull => 0
    | PresentInt(value) => value
    }

  switch right {
  | MissingName => fromLeft
  | PresentName(name) => fromLeft + String.length(name)
  }
}

type spreadBase = | SpreadOne(bool) | SpreadTwo

module SpreadSource = {
  type extra = | SpreadFive(int) | SpreadSix
}

type spreadCombined =
  | ...spreadBase
  | SpreadThree
  | ...SpreadSource.extra

let describeSpread = value =>
  switch value {
  | SpreadOne(flag) => if flag { "one" } else { "zero" }
  | SpreadTwo => "two"
  | SpreadThree => "three"
  | SpreadFive(value) => "five" ++ Int.toString(value)
  | SpreadSix => "six"
  }

@deriving(jsConverter)
type polyConverted = [
  | @as("x") #polyX
  | @as("hi") #polyHi
  | @as(`tick`) #polyTick
]

let convertPoly = value => {
  let jsValue = polyConvertedToJs(value)
  (jsValue, polyConvertedFromJs(jsValue))
}

@tag("kind")
type taggedInline =
  | TaggedPoint({x: int, y?: int})
  | TaggedName({name: string})

let describeTagged = value =>
  switch value {
  | TaggedPoint({x, y}) => x + y
  | TaggedPoint({x}) => x
  | TaggedName({name}) => String.length(name)
  }

@unboxed
type sourceSmall = | SmallText(string) | @as("fixed") SmallFixed

@unboxed
type sourceLarge =
  | SmallText(string)
  | @as("fixed") SmallFixed
  | @as(0) SmallZero
  | LargeObject({size: int})

let widenSmall = (value: sourceSmall): sourceLarge => (value :> sourceLarge)

module TellaPositionWidening = {
  type portraitPosition = [#Top | #Bottom]
  type layoutPosition = [#TopRight | #BottomRight | #TopLeft | #BottomLeft | #Top | #Bottom]

  let className = (position: layoutPosition) =>
    switch position {
    | #TopLeft | #Top => "top-left"
    | #TopRight => "top-right"
    | #BottomLeft => "bottom-left"
    | #BottomRight | #Bottom => "bottom-right"
    }

  let fromPortrait = (position: portraitPosition) =>
    className((position :> layoutPosition))
}

let allValues = (
  coercedValues,
  classifyJsonish(JsonFalse),
  classifyJsonish(JsonArray([1, 2, 3])),
  classifyJsonish(JsonObject({name: "box", count: 2})),
  mergeNullish(PresentInt(5), PresentName("ok")),
  describeSpread(SpreadFive(7)),
  convertPoly(#polyHi),
  describeTagged(TaggedPoint({x: 2, y: 3})),
  widenSmall(SmallFixed),
  TellaPositionWidening.fromPortrait(#Top),
  TellaPositionWidening.fromPortrait(#Bottom),
)
