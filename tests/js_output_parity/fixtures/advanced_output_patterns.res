%%raw(`
function outputParityHost(value) {
  return value
}

function outputParityOptional(name, value) {
  return name == null ? value : value + name.length
}

class OutputParityBox {
  constructor(value, label) {
    this.value = value
    this.label = label
  }

  read(index) {
    return [this.label, this.value + index]
  }
}
`)

type box

@new external makeBox: (int, string) => box = "OutputParityBox"
@send external readBox: (box, int) => (string, int) = "read"
@get external boxValue: box => int = "value"
@set external setBoxValue: (box, int) => unit = "value"

@variadic @val external maxMany: (int, array<int>) => int = "Math.max"
@variadic @new external newArray: (int, int, array<int>) => array<int> = "Array"
@val external hostValue: 'a => 'a = "outputParityHost"
@val external optionalHost: (~name: string=?, int) => int = "outputParityOptional"
@module("./math-tools.mjs") external importedAdd: (int, int) => int = "add"
@module({from: "./settings.json", with: {type_: "json", \"some-identifier": "ok"}})
external importedSettings: JSON.t = "default"

@val
external logUnwrapped: @unwrap
[
  | #Text(string)
  | #Count(int)
  | #Pair(string, int)
] => unit = "console.log"

type escapedRecord = {
  @as("class") className: string,
  @as("data-value") dataValue: int,
  mutable count: int,
}

@unboxed type single = Single(int)
type wrappedPayload = {value: int}
@unboxed type wrappedRecord = Wrapped(wrappedPayload)

exception Local(string, int)
exception Done

let useBox = () => {
  let box = makeBox(40, "box")
  setBoxValue(box, boxValue(box) + 2)
  readBox(box, 3)
}

let useVariadic = values => {
  let fromNew = newArray(1, 2, values)
  (maxMany(0, fromNew), fromNew)
}

let useOptional = maybeName => optionalHost(~name=?maybeName, 10)

let useUnwrap = value =>
  switch value {
  | 0 => logUnwrapped(#Text("zero"))
  | 1 => logUnwrapped(#Pair("one", 1))
  | _ => logUnwrapped(#Count(value))
  }

let updateEscapedRecord = record => {
  record.count = record.count + 1
  {...record, dataValue: record.dataValue + record.count}
}

let unboxedValue = value =>
  switch Single(value) {
  | Single(inner) => inner + 1
  }

let wrappedValue = value =>
  switch Wrapped({value}) {
  | Wrapped({value}) => value * 2
  }

let exceptionValue = value =>
  try {
    if value > 0 {
      throw(Local("positive", value))
    } else if value == 0 {
      throw(Done)
    }
    #Negative(value)
  } catch {
  | Local("positive", payload) => #Positive(payload)
  | Done => #Done
  | _ => #Other
  }

external ignorePromise: promise<'a> => unit = "%identity"

let asyncValue = async value => {
  let resolved = await Promise.resolve(value + 1)
  resolved * 2
}

let asyncNested = () =>
  (
    async () => {
      let value = await asyncValue(3)
      Console.log(value)
    }
  )()->ignorePromise

module Included = {
  let base = 41
  let add = value => value + base
}

module WithInclude = {
  include Included
  let result = add(1)
}

module type Seed = {
  let seed: int
}

module Make = (Input: Seed) => {
  let value = Input.seed + WithInclude.result
}

module Made = Make({
  let seed = 1
})

let importedValue = importedAdd(Made.value, hostValue(1))
let settingsValue = importedSettings
let bigintValue = 1000n + 24n
let assertionValue = () => assert(false)
