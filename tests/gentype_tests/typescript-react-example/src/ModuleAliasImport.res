// A module alias re-exports the imported types of the aliased module, with
// the import path and name of their `@genType.import` tuple payload.
module Imported = ImportedTypes

@genType
let keep = (x: Imported.num) => x

@genType
let keepEither = (x: Imported.numberOrString) => x
