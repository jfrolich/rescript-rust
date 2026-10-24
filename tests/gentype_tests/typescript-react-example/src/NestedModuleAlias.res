// An alias of a module nested in another unit re-exports that module's
// types, like an alias of a whole unit.
module Transcript = NestedTypes.Transcript

@genType
let words = (data: Transcript.data) => data.words->Array.length
