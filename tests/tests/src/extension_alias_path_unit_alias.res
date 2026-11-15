// Extension constructors of another unit read through a module alias.
module A = Extension_alias_path_unit

let e = A.E(1)
let c = A.C(2)
let f = exn =>
  switch exn {
  | A.E(n) => n
  | _ => 0
  }
