// The @obj argument type appears in both the arrow and the object result,
// so OCaml's unused-attribute sweep reports @as twice.
@obj external mk: (~a: int=?, ~b: @as("bb") string) => _ = ""
