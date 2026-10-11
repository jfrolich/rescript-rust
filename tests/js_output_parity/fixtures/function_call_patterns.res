@@uncurried

%%raw(`
function outputParityCallUnit(callback) {
  callback()
  return 1
}

function outputParityUseIgnored(value, callback) {
  return callback(value, value + 1)
}

function outputParityUseAs(value, _fixed, callback) {
  return callback(value, value + 2)
}
`)

@val external mapInts: (array<int>, int => int) => array<int> = "Array.prototype.map.call"
@val external callUnit: (unit => unit) => int = "outputParityCallUnit"
@val external useIgnored: (int, @ignore int, (int, int) => int) => int =
  "outputParityUseIgnored"
@val external useAsInt: (int, @as(3) _, (int, int) => int) => int = "outputParityUseAs"
@val external optionalCallback: (
  (string, ~props: int=?, array<int>) => int,
  string,
) => int = "outputParityOptionalCallback"

let add2 = (x, y) => x + y
let add3 = (x, y, z) => x + y + z

let partialLeft = add2(10, ...)
let partialMiddle = add3(_, 2, 3)
let partialTail = add3(1, ...)

let labelled = (~x, ~y=2, ~z) => x + y + z
let labelledPartial = labelled(~z=10, ...)
let labelledResults = (
  labelledPartial(~x=1),
  labelledPartial(~x=1, ~y=5),
  labelled(~x=1, ~z=3),
)

let pipeCalls = (
  3->add2(4),
  5->partialLeft,
  6->partialMiddle,
)

let callbackCalls = (
  mapInts([1, 2, 3], value => value + 1),
  useIgnored(4, 99, (left, right) => left + right),
  useAsInt(4, (left, right) => left + right),
)

let unitCall = () =>
  callUnit((() as value) =>
    if value == () {
      Console.log("unit")
    }
  )

let higherOrder = callback => callback(1, 2)
let directCallback = higherOrder(add2)
let wrappedCallback = higherOrder((left, right) => add3(left, right, 3))

let optionalCallbackValue =
  optionalCallback(
    (name, ~props=?, values) =>
      name->String.length + props->Option.getOr(0) + Array.length(values),
    "name",
  )

let allValues = (
  partialLeft(2),
  partialMiddle(1),
  partialTail(2, 3),
  labelledResults,
  pipeCalls,
  callbackCalls,
  unitCall(),
  directCallback,
  wrappedCallback,
  optionalCallbackValue,
)
