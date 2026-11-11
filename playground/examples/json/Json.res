open Macro

// A @generic is called like a function: Json.encode(user). When the type
// of the argument is known, the compiler runs it with that type and makes
// a function of the result: one per type, shared by all the calls.
@generic
let encode = (value: code<'a>): code<JSON.t> =>
  switch Type.info(typeOf(value)) {
  | String => %code(JSON.Encode.string(${value}))
  | Int => %code(JSON.Encode.int(${value}))
  | Float => %code(JSON.Encode.float(${value}))
  | Bool => %code(JSON.Encode.bool(${value}))
  | Option(_) =>
    %code(
      switch ${value} {
      | Some(v) => encode(v)
      | None => JSON.Encode.null
      }
    )
  | Array(_) => %code(JSON.Encode.array(${value}->Array.map(v => encode(v))))
  | Record({fields}) =>
    let entries = fields->Array.map(f => {
      // @Json.key("...") on a field renames it.
      let key = f.attrs->Attr.string("Json.key")->Option.getOr(f.jsName)
      %code((${Code.string(key)}, encode(${value->Code.field(f.name)})))
    })
    %code(JSON.Encode.object(Dict.fromArray(${Code.array(entries)})))
  | Variant({constructors}) =>
    Code.switch_(
      value,
      constructors->Array.map(c => {
        let (pattern, args) = Pat.constructor(c)
        let fields = args->Array.mapWithIndex((arg, i) => {
          let key = switch c.fields[i] {
          | Some(field) => field.name
          | None => "_" ++ Int.toString(i)
          }
          %code((${Code.string(key)}, encode(${arg})))
        })
        let tag = %code(("tag", JSON.Encode.string(${Code.string(c.name)})))
        (pattern, %code(JSON.Encode.object(Dict.fromArray(${Code.array([tag, ...fields])}))))
      }),
    )
  | Abstract({name}) =>
    // A type from elsewhere says how it is encoded with a toJson next to it.
    switch Type.companion(typeOf(value), "toJson") {
    | Some(toJson) => %code(${toJson}(${value}))
    | None => error(`${name} is abstract and its module has no toJson`)
    }
  | _ => error(`Json.encode cannot encode the type ${Type.name(typeOf(value))}`)
  }
