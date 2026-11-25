// A record pattern's rest reads the labels the file declares for a type of
// the rest type's name. The alias of a record type declares none, so its
// rest reads no label: `SubConfig.t`'s labels stay dead.

type config = {name: string, version: string, debug: bool}

module SubConfig = {
  type t = {version: string, debug: bool}
}

type aliasedSubConfig = SubConfig.t

@live
let getAliasedRest = (config: config) =>
  switch config {
  | {name: _, ...aliasedSubConfig as rest} => rest
  }

type wholeConfig = {name: string, version: string, debug: bool}

// The rest of the whole type reads every label, in the order the table of
// declarations lists them.
@live
let getWholeRest = ({...wholeConfig as rest}: wholeConfig) => rest
