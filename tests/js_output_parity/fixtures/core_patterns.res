type point = {
  x: int,
  y: int,
  label?: string,
}

type action =
  | Add(int)
  | Rename(string)
  | Reset

type unboxed =
  | @as(0) Empty
  | @as(1) One
  | Value(int)

type poly = [#ready | #failed(string)]

let tupleValue = (1, "two", true)
let listValue = list{1, 2, 3}
let arrayValue = [1, 2, 3]
let recordValue = {x: 1, y: 2, label: "origin"}
let recordUpdate = {...recordValue, x: recordValue.x + 1}
let objectValue = {"x": recordValue.x, "label": recordValue.label}
let dictValue = Dict.fromArray([("one", 1), ("two", 2)])

let labelled = (~x, ~y=2, ()) => x + y
let optional = (~x=?, ()) =>
  switch x {
  | Some(value) => value
  | None => 0
  }

let pipeResult = 1->(x => x + 1)

let controlFlow = (action, limit) => {
  let total = ref(0)

  for i in 0 to limit {
    total := total.contents + i
  }

  while total.contents < 3 {
    total := total.contents + 1
  }

  switch action {
  | Add(value) when value > 0 => total.contents + value
  | Rename(name) => String.length(name)
  | Reset | Add(_) => 0
  }
}

let tryValue = value =>
  try {
    assert(value >= 0)
    value + 1
  } catch {
  | _ => 0
  }

let patternValue = value =>
  switch value {
  | Some((left, right)) if left < right => left + right
  | Some((left, _)) => left
  | None => 0
  }

let polyValue: poly = #failed("network")
let polyResult =
  switch polyValue {
  | #ready => 1
  | #failed(message) => String.length(message)
  }

let unboxedValue = Value(10)
let unboxedResult =
  switch unboxedValue {
  | Empty => 0
  | One => 1
  | Value(value) => value
  }

let nestedModules = {
  module Inner = {
    let make = value => value + labelled(~x=value, ())
  }

  Inner.make(3)
}
