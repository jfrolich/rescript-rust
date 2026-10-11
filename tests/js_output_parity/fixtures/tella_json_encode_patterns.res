type encoder<'a> = 'a => JSON.t

@val external jsonNull: JSON.t = "null"
external jsonString: string => JSON.t = "%identity"
external jsonFloat: float => JSON.t = "%identity"
external jsonInt: int => JSON.t = "%identity"
external jsonBool: bool => JSON.t = "%identity"
external jsonDict: dict<JSON.t> => JSON.t = "%identity"
external jsonArray: array<JSON.t> => JSON.t = "%identity"
external stringArray: array<string> => JSON.t = "%identity"
external numberArray: array<float> => JSON.t = "%identity"
external boolArray: array<bool> => JSON.t = "%identity"

let char = value => value->String.make->jsonString

let nullable = (encode, value) =>
  switch value {
  | None => jsonNull
  | Some(value) => encode(value)
  }

let withDefault = (fallback, encode, value) =>
  switch value {
  | None => fallback
  | Some(value) => encode(value)
  }

let dict = (encode, values) => {
  let pairs = Dict.toArray(values)
  let encodedPairs = pairs->Array.map(((key, value)) => (key, encode(value)))
  jsonDict(Dict.fromArray(encodedPairs))
}

let object_ = (props): JSON.t => props->List.toArray->Dict.fromArray->jsonDict

let array = (encode, values) => values->Array.map(encode)->jsonArray

let list = (encode, values) =>
  switch values {
  | list{} => jsonArray([])
  | list{head, ...tail} as fullList =>
    let output = Array.make(~length=List.length(fullList), encode(head))
    let rec fill = (index, remaining) =>
      switch remaining {
      | list{} => output
      | list{head, ...tail} =>
        Array.setUnsafe(output, index, encode(head))
        fill(index + 1, tail)
      }

    jsonArray(fill(1, tail))
  }

let pair = (encodeA, encodeB, (left, right)) => jsonArray([encodeA(left), encodeB(right)])
let tuple2 = pair
let tuple3 = (encodeA, encodeB, encodeC, (a, b, c)) =>
  jsonArray([encodeA(a), encodeB(b), encodeC(c)])
let tuple4 = (encodeA, encodeB, encodeC, encodeD, (a, b, c, d)) =>
  jsonArray([encodeA(a), encodeB(b), encodeC(c), encodeD(d)])

let sourceDict = Dict.fromArray([("name", "Tella"), ("kind", "video")])

let encodedNullable = nullable(jsonString, Some("present"))
let encodedDefault = withDefault(jsonNull, jsonInt, None)
let encodedDict = dict(jsonString, sourceDict)
let encodedObject = object_(list{("id", jsonString("story")), ("ready", jsonBool(true))})
let encodedArray = array(jsonInt, [1, 2, 3])
let encodedList = list(jsonString, list{"record", "share", "export"})
let encodedPair = pair(jsonString, jsonInt, ("views", 42))
let encodedTuple2 = tuple2(jsonString, jsonBool, ("enabled", true))
let encodedTuple3 = tuple3(jsonString, jsonFloat, jsonBool, ("duration", 12.5, true))
let encodedTuple4 = tuple4(jsonString, jsonInt, jsonFloat, jsonBool, ("clip", 7, 4.5, false))
let encodedPrimitiveArrays = (stringArray(["a", "b"]), numberArray([1.0, 2.0]), boolArray([true]))
let encodedChar = char('x')

let output = (
  encodedNullable,
  encodedDefault,
  encodedDict,
  encodedObject,
  encodedArray,
  encodedList,
  encodedPair,
  encodedTuple2,
  encodedTuple3,
  encodedTuple4,
  encodedPrimitiveArrays,
  encodedChar,
)
