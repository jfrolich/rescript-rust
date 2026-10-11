// Field access through a local alias to a unit whose type re-exports another
// unit's record under the same name: `P.t` expands to the record, not to itself.
module P = Alias_manifest_same_name_reexport

let get = (v: P.t) => v.x
let label = (v: P.t) => v.label
let value: P.t = {x: 1, label: "one"}

let total = get(value) + String.length(label(value))
