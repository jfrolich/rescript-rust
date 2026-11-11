open Macro

exception DecodeError(string)
let fail = (message: string) => throw(DecodeError(message))

let field = (json: JSON.t, key: string): JSON.t =>
  switch json {
  | Object(fields) => fields->Dict.get(key)->Option.getOr(JSON.Null)
  | _ => fail(`expected an object with the field "${key}"`)
  }

// The result type of this @generic is a type variable: nothing in the
// arguments says what to decode to. `expected()` is the type the call site
// wants, so the annotation `let user: user = ...` picks the decoder.
@generic
let fromJson = (json: code<JSON.t>): code<'a> =>
  switch Type.info(expected()) {
  | String =>
    %code(
      switch ${json} {
      | String(text) => text
      | _ => fail("expected a string")
      }
    )
  | Int =>
    %code(
      switch ${json} {
      | Number(number) => Float.toInt(number)
      | _ => fail("expected a number")
      }
    )
  | Bool =>
    %code(
      switch ${json} {
      | Boolean(bool) => bool
      | _ => fail("expected true or false")
      }
    )
  | Option(inner) =>
    %code(
      switch ${json} {
      | Null => None
      | present => Some((fromJson(present): ${inner}))
      }
    )
  | Array(inner) =>
    %code(
      switch ${json} {
      | Array(items) => items->Array.map(item => (fromJson(item): ${inner}))
      | _ => fail("expected an array")
      }
    )
  | Record({fields}) =>
    Code.record(
      fields->Array.map(f => (
        f.name,
        %code((fromJson(field(${json}, ${Code.string(f.jsName)})): ${f.typ})),
      )),
    )
  | _ => error(`Decode.fromJson cannot decode to ${Type.name(expected())}`)
  }
