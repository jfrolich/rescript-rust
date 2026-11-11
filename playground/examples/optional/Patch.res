open Macro

// The type of an optional field is the type of `value.field`: for
// `nickname?: string` that is option<string>. Reading the field, writing it
// with Code.entryOf and declaring it with Type.record all agree on it, so a
// macro needs no special case to be right for optional fields.

// %Patch.t(user): the record type with every field optional.
// Type.optional leaves a field that is optional already as it is.
@macro
let t = (source: typ): typ =>
  switch Type.info(source) {
  | Record({fields}) => Type.record(fields->Array.map(Type.optional))
  | _ => error(`Patch.t needs a record type, and ${Type.name(source)} is not one`)
  }

// Patch.apply(value, patch): the record with the fields of the patch that
// have a value.
@generic
let apply = (value: code<'a>, patch: code<'p>): code<'a> =>
  switch Type.info(typeOf(value)) {
  | Record({fields}) =>
    Code.record(
      fields->Array.map(f => {
        let current = value->Code.field(f.name)
        let change = patch->Code.field(f.name)
        // entryOf takes a value of the type f.typ. It writes `name: value`,
        // and `name: ?value` for an optional field, which leaves the field
        // out of the record when the value is None.
        Code.entryOf(
          f,
          f.optional ? %code(Option.orElse(${change}, ${current})) : %code(Option.getOr(${change}, ${current})),
        )
      }),
    )
  | _ => error("Patch.apply needs a record")
  }
