open Macro

// Convert.to(value) is a record of the type the call site expects, filled
// from the fields of `value` that have the same names.
//
// Which fields there are is known when the macro runs, not when it is
// written, so the record cannot be one quote. It is built from entries, one
// per field: Code.entry(name, value) is `name: value`.
@generic
let to = (value: code<'a>): code<'b> =>
  switch (Type.info(typeOf(value)), Type.info(expected())) {
  | (Record({fields: sources}), Record({fields: targets})) =>
    Code.record(
      targets->Array.filterMap(target => {
        let read = value->Code.field(target.name)
        switch sources->Array.find(source => source.name == target.name) {
        // `name: value.name`
        | Some({optional: false}) => Some(Code.entry(target.name, read))
        // Optional on both sides: `name: ?value.name` passes on an option,
        // and leaves the field out when there is no value.
        | Some(_) if target.optional => Some(Code.entry(target.name, read, ~optional=true))
        | Some(_) =>
          error(`Convert.to: ${target.name} is optional in ${Type.name(typeOf(value))} and required in ${Type.name(expected())}`)
        // A field that is not there stays out when it may.
        | None if target.optional => None
        | None => error(`Convert.to: ${Type.name(typeOf(value))} has no field ${target.name}`)
        }
      }),
    )
  | _ => error("Convert.to converts a record to a record")
  }
