open Macro

// A macro in a type position takes types and returns a type.
@macro
let t = (source: typ): typ =>
  switch Type.info(source) {
  | Record({fields}) => Type.record(fields->Array.map(f => {...f, optional: true}))
  | _ => error(`Partial.t needs a record type, and ${Type.name(source)} is not one`)
  }
