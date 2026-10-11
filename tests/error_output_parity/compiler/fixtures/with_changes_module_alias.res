// error-output-parity: Typemod.With_changes_module_alias
module type S = {
  module A: {type t}
  module B = A
}

module type T = S with type A.t := int
