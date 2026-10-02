// A field of a record reached through the unit's own path keeps that path,
// even when a local alias of the record's module is in scope.
open Field_alias_scope_types
module ServerEvent = {
  module Legacy = Field_alias_scope_types.Legacy
  let settle = (e: outbound) =>
    switch e {
    | Legacy(DuplicateScene(payload)) => payload.completion->Option.forEach(c => c(Error("x")))
    | _ => ()
    }
}
