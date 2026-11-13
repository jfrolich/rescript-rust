@unboxed
type rec t =
  | Boolean(bool)
  | @as(null) Null
  | String(string)
  | Number(float)
  | Object(dict<t>)
  | Array(array<t>)

@unboxed
type replacer = Keys(array<string>) | Replacer((string, t) => t)

@pure @throws @val external parseOrThrow: (string, ~reviver: (string, t) => t=?) => t = "JSON.parse"

@pure @val
external stringify: (t, ~replacer: replacer=?, ~space: int=?) => string = "JSON.stringify"

@throws @val @pure
external stringifyAny: ('a, ~replacer: replacer=?, ~space: int=?) => option<string> =
  "JSON.stringify"

module Encode = {
  @pure
  external bool: bool => t = "%identity"

  @pure
  external null: t = "#null"

  @pure
  external string: string => t = "%identity"

  @pure
  external int: int => t = "%identity"

  @pure
  external float: float => t = "%identity"

  @pure
  external object: dict<t> => t = "%identity"

  @pure
  external array: array<t> => t = "%identity"

  @pure
  external stringArray: array<string> => t = "%identity"

  @pure
  external floatArray: array<float> => t = "%identity"

  @pure
  external intArray: array<int> => t = "%identity"

  @pure
  external boolArray: array<bool> => t = "%identity"

  @pure
  external objectArray: array<dict<t>> => t = "%identity"
}

module Decode = {
  let bool = json =>
    switch json {
    | Boolean(b) => Some(b)
    | _ => None
    }

  let null = json =>
    switch json {
    | Null => Some(Stdlib_Null.null)
    | _ => None
    }

  let string = json =>
    switch json {
    | String(s) => Some(s)
    | _ => None
    }

  let float = json =>
    switch json {
    | Number(f) => Some(f)
    | _ => None
    }

  let object = json =>
    switch json {
    | Object(o) => Some(o)
    | _ => None
    }

  let array = (json: t) =>
    switch json {
    | Array(a) => Some(a)
    | _ => None
    }
}

@pure
external ignore: t => unit = "%ignore"
