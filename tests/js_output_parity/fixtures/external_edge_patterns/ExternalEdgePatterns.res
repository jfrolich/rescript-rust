%%raw(`
var outputParityRoot = {
  version: "1.0.0",
  nested: {
    count: 7
  },
  bump(value) {
    return value + 1
  },
  route(state, title, href) {
    return [state, title, href].join(":")
  }
}

function outputParityMaybe(flag) {
  return flag ? "present" : null
}

function outputParityMaybeEither(flag) {
  return flag ? undefined : "present"
}

function outputParityString(flag) {
  return flag
}

function outputParityInt(flag) {
  return flag
}

function outputParityTagged(strings, ...values) {
  return strings.join("|") + "::" + values.join("|")
}

function outputParityCallWithReceiver(callback) {
  return callback({base: 5}, 3)
}
`)

type router
type element

@val @scope("outputParityRoot") external scopedVersion: string = "version"
@val @scope(("outputParityRoot", "nested")) external nestedCount: int = "count"
@scope("outputParityRoot") external scopedBump: int => int = "bump"
@scope("outputParityRoot")
external route: (@as(json`null`) _, @as("") _, ~href: string) => string = "route"

@val @return(nullable) external maybeNullable: bool => option<string> = "outputParityMaybe"
@val
@return(null_undefined_to_opt)
external maybeNullUndefined: bool => option<string> = "outputParityMaybeEither"

@val
external marshalString: @string
[
  | @as("enabled") #enabled
  | @as("disabled") #disabled
] => string = "outputParityString"

@val
external marshalInt: @int
[
  | @as(1) #one
  | @as(3) #three
  | @as(5) #five
] => int = "outputParityInt"

@val external tagged: taggedTemplate<int, string> = "outputParityTagged"
external asTaggedTemplate: ((array<string>, array<int>) => string) => taggedTemplate<int, string> =
  "%identity"

@val
external callWithReceiver: (({"base": int}, int) => int) => int =
  "outputParityCallWithReceiver"

let taggedValue = tagged`left ${1} middle ${2} right`

let localTagged = asTaggedTemplate((strings, values) => {
  let result = ref("")
  let valueCount = values->Array.length
  for index in 0 to valueCount - 1 {
    result :=
      result.contents ++
      strings->Array.getUnsafe(index) ++
      values->Array.getUnsafe(index)->Int.toString
  }
  result.contents ++ strings->Array.getUnsafe(valueCount)
})

let localTaggedValue = localTagged`a${1}b${2}c`

let receiverReader = (receiver: {"length": int, "offset": int}, left, right) =>
  receiver["length"] + receiver["offset"] + left + right

let receiverCallbackValue = callWithReceiver((receiver, amount) => receiver["base"] + amount)

type box = {
  mutable value: int,
}

@get @return(nullable) external currentElement: box => option<element> = "current"
@set external setStatus: (box, @as(200) _) => unit = "status"

let boxOps = box => {
  setStatus(box)
  switch currentElement(box) {
  | Some(_) => box.value + 1
  | None => box.value
  }
}

module type RuntimeCollectionsType = module type of RuntimeCollections

let dynamicForEach = async values => {
  let forEach = await import(RuntimeCollections.forEach)
  values->forEach(value => Console.log(value))
}

let dynamicModuleLength = async () => {
  module Collections = await (RuntimeCollections: RuntimeCollectionsType)
  Collections.length(list{1, 2, 3})
}

let allValues = (
  scopedVersion,
  nestedCount,
  scopedBump(41),
  route(~href="/settings"),
  maybeNullable(false),
  maybeNullUndefined(true),
  marshalString(#enabled),
  marshalInt(#three),
  taggedValue,
  localTaggedValue,
  receiverReader,
  receiverCallbackValue,
  boxOps({value: 10}),
  dynamicForEach([1, 2, 3]),
  dynamicModuleLength(),
)
