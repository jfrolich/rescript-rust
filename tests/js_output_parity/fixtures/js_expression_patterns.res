%%raw(`
function outputParityOptionalValue(x, y) {
  return (x === undefined ? 10 : x) + y
}

class OutputParityBag {
  constructor(...items) {
    this.items = items
  }

  add(...items) {
    this.items.push(...items)
    return this.items.length
  }

  switch() {
    return this.items.length
  }
}

const outputParityScope = {
  nested: {
    value: 41,
    bump(value) {
      return value + 1
    }
  }
}
`)

type token
type bag

type rec kind<_> =
  | Int: kind<int>
  | Str: kind<string>

@obj
external makeConfig: (
  ~kind: @ignore kind<'a>,
  ~name: string,
  ~value: 'a,
  ~enabled: @as(json`true`) _,
  ~empty: @as(json`null`) _,
  unit,
) => _ = ""

@val external optionalValue: (~x: int=?, ~y: int, unit) => int = "outputParityOptionalValue"
@new @variadic external makeBag: array<int> => bag = "OutputParityBag"
@send @variadic external addBag: (bag, int, array<int>) => int = "add"
@get external bagItems: bag => array<int> = "items"
@get_index external getItem: (array<int>, int) => option<int> = ""
@set_index external setItem: (array<int>, int, int) => unit = ""
@send external \"switch": bag => int = "switch"

@module("keyword-module") external defaultToken: token = "default"
@module("keyword-module") external classToken: token = "class"

@val @scope(("outputParityScope", "nested")) external scopedValue: int = "value"
@scope(("outputParityScope", "nested")) external scopedBump: int => int = "bump"

let configValues = (
  makeConfig(~kind=Int, ~name="count", ~value=3, ()),
  makeConfig(~kind=Str, ~name="label", ~value="three", ()),
)

let optionalCounter = ref(0)

let nextOptional = () => {
  optionalCounter := optionalCounter.contents + 1
  Some(optionalCounter.contents)
}

let optionalCalls = () => (
  optionalValue(~y=2, ()),
  optionalValue(~x=3, ~y=2, ()),
  optionalValue(~x=?nextOptional(), ~y=2, ()),
  optionalCounter.contents,
)

let mutateBag = values => {
  let bag = makeBag(values)
  let lengthAfterAdd = bag->addBag(0, [1, 2])
  let items = bagItems(bag)
  setItem(items, 0, lengthAfterAdd)

  switch getItem(items, 0) {
  | Some(first) => (first, \"switch"(bag))
  | None => (0, 0)
  }
}

let keywordObject = (window, defaultValue) => {
  "window": window,
  "default": defaultValue,
  "case": 3,
  "data-value": 4,
}

let readKeywordObject = value => (
  value["window"],
  value["default"],
  value["case"],
  value["data-value"],
)

let decodeJson = json =>
  switch json {
  | JSON.Object(dict{
      "type": JSON.String("count"),
      "value": JSON.Number(value),
    }) =>
    Float.toInt(value)
  | JSON.Object(dict{"type": JSON.String("name"), "value": JSON.String(name)}) =>
    String.length(name)
  | JSON.Object(dict{"type": JSON.String("empty")}) => 0
  | _ => -1
  }

let allValues = (
  configValues,
  optionalCalls(),
  mutateBag([5, 6]),
  keywordObject(defaultToken, classToken),
  readKeywordObject(keywordObject(defaultToken, classToken)),
  scopedBump(scopedValue),
  decodeJson(JSON.parseOrThrow(`{"type":"count","value":3}`)),
)
