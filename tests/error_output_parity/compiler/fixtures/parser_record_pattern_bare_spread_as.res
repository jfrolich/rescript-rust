// A spread without a type or name recovers like OCaml's row parser.
type source={a:int}
let getRest=({...as rest}:source)=>rest
