@inline let inlineText = "attribute"
@inline let inlineFlag = true
@inline let inlineInt = 7

@inline
let classifyStatus = code =>
  switch code {
  | 200 | 201 => "ok"
  | 400 | 404 | 500 | 503 => "error"
  | _ => "other"
  }

@inline(never)
let noInlineIncrement = value => value + 1

module type Mapper = {
  let map: int => int
}

@inline(always)
module MakeInline = (Input: Mapper) => {
  let result = Input.map(inlineInt)
}

module InlineMade = MakeInline({
  let map = value => value + 3
})

%%private(let hiddenBase = 41)

%%private(
  let hiddenPair = (hiddenBase, hiddenBase + 1)
  let hiddenAdd = (left, right) => left + right + hiddenBase
)

module PrivateModule = {
  %%private(let localHidden = 3)
  let localUse = localHidden + hiddenBase
}

let privateValue = {
  let (left, right) = hiddenPair
  hiddenAdd(left, right) + PrivateModule.localUse
}

@val @module(("attribute-parity", "Nested"))
external tupleImportedValue: int = "value"

@module(("attribute-parity", "Nested"))
external tupleImportedCall: int => int = "bump"

@val @module(("attribute-parity", "Nested"))
external tupleImportedName: string = "name"

type reader

@send
@return({null_to_opt: null_to_opt})
external readLegacyNull: (reader, string) => option<int> = "read"

@get_index @return(null_to_opt) external readNullIndex: (array<int>, int) => option<int> = ""

let nullToOptValue = (target, values) => {
  let fromReader =
    switch target->readLegacyNull("count") {
    | Some(value) => value
    | None => 0
    }
  let fromIndex =
    switch readNullIndex(values, 0) {
    | Some(value) => value
    | None => 0
    }
  fromReader + fromIndex
}

@val
external logUnwrappedNamed: (
  ~req: @unwrap [#String(string) | #Int(int)],
  ~opt: @unwrap [#String(string) | #Bool(bool)]=?,
  unit,
) => unit = "console.log"

@val external logUnwrappedOptional: (~h: @unwrap [#A(int) | #B(string)]=?, int) => unit =
  "console.log"

let unwrapCalls = optionalChoice => {
  logUnwrappedNamed(~req=#Int(1), ())
  logUnwrappedNamed(~req=#String("two"), ~opt=#Bool(true), ())
  logUnwrappedNamed(~req=#Int(3), ~opt=?optionalChoice, ())
  logUnwrappedOptional(~h=?Some(#A(4)), 5)
  logUnwrappedOptional(~h=?None, 6)
}

let allValues = (
  inlineText,
  inlineFlag,
  inlineInt,
  classifyStatus(200),
  classifyStatus(500),
  noInlineIncrement(inlineInt),
  InlineMade.result,
  privateValue,
  tupleImportedCall(tupleImportedValue),
  tupleImportedName,
  nullToOptValue,
  unwrapCalls,
)
