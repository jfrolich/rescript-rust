// Record patterns collect Ambiguous_name warnings and report them for the
// whole pattern (disambiguate_record_elem_list, closed = false).
type t = {x: int, y: int}
type r = {x: int, y?: int, z: int}

let testMatch = v =>
  switch v {
  | {y} => y
  }

module M = {
  type a = {k: int}
  type b = {k: int, l: int}
}
let {M.k: k, _} = {M.k: 1}
