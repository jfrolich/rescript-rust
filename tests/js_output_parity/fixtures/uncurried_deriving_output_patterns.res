@@uncurried

@deriving(accessors)
type point = {
  x: int,
  y: int,
}

@deriving(accessors)
type action =
  | Reset
  | Move(int, int)
  | Rename(string)

let xAccessor: point => int = x
let yAccessor: point => int = y
let resetValue: action = reset
let moveAccessor: (int, int) => action = move
let renameAccessor: string => action = rename

let compose = (value, accessor) => accessor(value)

let pointValue = {x: 1, y: 2}

let derivedValues = (
  xAccessor(pointValue),
  yAccessor(pointValue),
  resetValue,
  moveAccessor(3, 4),
  renameAccessor("next"),
  compose(pointValue, x),
  compose(5, value => move(value, value + 1)),
)
