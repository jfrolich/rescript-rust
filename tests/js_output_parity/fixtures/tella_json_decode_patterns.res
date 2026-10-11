@new external makeUninitializedArray: int => array<'a> = "Array"

@val external stringify: JSON.t => string = "JSON.stringify"

type decoder<'a> = JSON.t => 'a

exception DecodeError(string)

let number = json =>
  if typeof(json) == #number {
    (Obj.magic((json: JSON.t)): float)
  } else {
    throw(DecodeError("Expected number, got " ++ stringify(json)))
  }

let negativeNumber = json => {
  let value = number(json)
  if value < 0.0 {
    value
  } else {
    throw(DecodeError("Expected negative number"))
  }
}

let string = json =>
  if typeof(json) == #string {
    (Obj.magic((json: JSON.t)): string)
  } else {
    throw(DecodeError("Expected string, got " ++ stringify(json)))
  }

let array = (decode: decoder<'a>, json): array<'a> =>
  if Array.isArray(json) {
    let source: array<JSON.t> = Obj.magic((json: JSON.t))
    let length = Array.length(source)
    let target = makeUninitializedArray(length)

    for index in 0 to length - 1 {
      let value =
        try {
          decode(Array.getUnsafe(source, index))
        } catch {
        | DecodeError(message) =>
          throw(DecodeError(message ++ ("\n\tin array at index " ++ Int.toString(index))))
        }

      Array.setUnsafe(target, index, value)
    }

    target
  } else {
    throw(DecodeError("Expected array, got " ++ stringify(json)))
  }

let tuple3 = (decodeA, decodeB, decodeC, json) =>
  if Array.isArray(json) {
    let source: array<JSON.t> = Obj.magic((json: JSON.t))
    let length = Array.length(source)
    if length == 3 {
      try {
        (
          decodeA(Array.getUnsafe(source, 0)),
          decodeB(Array.getUnsafe(source, 1)),
          decodeC(Array.getUnsafe(source, 2)),
        )
      } catch {
      | DecodeError(message) => throw(DecodeError(message ++ "\n\tin tuple3"))
      }
    } else {
      throw(DecodeError("Expected array of length 3, got array of length " ++ Int.toString(length)))
    }
  } else {
    throw(DecodeError("Expected array, got " ++ stringify(json)))
  }

let dict = (decode: decoder<'a>, json): dict<'a> =>
  if typeof(json) == #object && !Array.isArray(json) && !Nullable.isNullable(Obj.magic(json)) {
    let source: dict<JSON.t> = Obj.magic((json: JSON.t))
    let keys = Dict.keysToArray(source)
    let length = Array.length(keys)
    let target = dict{}

    for index in 0 to length - 1 {
      let key = Array.getUnsafe(keys, index)
      let value =
        try {
          decode(Dict.getUnsafe(source, key))
        } catch {
        | DecodeError(message) => throw(DecodeError(message ++ "\n\tin dict"))
        }

      Dict.set(target, key, value)
    }

    target
  } else {
    throw(DecodeError("Expected object, got " ++ stringify(json)))
  }

let field = (key, decode, json) =>
  if typeof(json) == #object && !Array.isArray(json) && !Nullable.isNullable(Obj.magic(json)) {
    let source: dict<JSON.t> = Obj.magic((json: JSON.t))
    switch Dict.get(source, key) {
    | Some(value) =>
      try {
        decode(value)
      } catch {
      | DecodeError(message) => throw(DecodeError(message ++ ("\n\tat field '" ++ (key ++ "'"))))
      }
    | None => throw(DecodeError("Expected field '" ++ (key ++ "'")))
    }
  } else {
    throw(DecodeError("Expected object, got " ++ stringify(json)))
  }

let rec at = (keyPath, decode, json) =>
  switch keyPath {
  | list{key} => field(key, decode, json)
  | list{first, ...rest} => field(first, at(rest, decode, ...), json)
  | list{} => throw(Invalid_argument("Expected keyPath to contain at least one element"))
  }

let optional = (decode, json) =>
  try {
    Some(decode(json))
  } catch {
  | DecodeError(_) => None
  }

let oneOf = (decoders, json) => {
  let rec loop = (decoders, errors) =>
    switch decoders {
    | list{} =>
      let formattedErrors = "\n- " ++ Array.join(List.toArray(List.reverse(errors)), "\n- ")
      throw(
        DecodeError(
          "All decoders failed: " ++ (formattedErrors ++ ("\nJSON: " ++ stringify(json))),
        ),
      )
    | list{decode, ...rest} =>
      try {
        decode(json)
      } catch {
      | DecodeError(message) => loop(rest, list{message, ...errors})
      }
    }

  loop(decoders, list{})
}

let parsedArray = JSON.parseOrThrow(`[1,2,3]`)
let parsedObject = JSON.parseOrThrow(`{"name":"Tella","stats":{"views":42},"tags":["video","share"]}`)

let decodedNumbers = array(number, parsedArray)
let decodedTuple = tuple3(number, number, number, parsedArray)
let decodedDict = dict(string, JSON.parseOrThrow(`{"first":"one","second":"two"}`))
let decodedNested = at(list{"stats", "views"}, number, parsedObject)
let decodedOptional = optional(string, parsedArray)
let decodedOneOf = oneOf(list{negativeNumber, number}, JSON.parseOrThrow(`42`))

let output = (
  decodedNumbers,
  decodedTuple,
  decodedDict,
  decodedNested,
  decodedOptional,
  decodedOneOf,
)
