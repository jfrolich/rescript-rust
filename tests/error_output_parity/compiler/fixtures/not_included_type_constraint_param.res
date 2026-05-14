// error-output-parity: Includecore.Constraint via concrete type parameters in Typemod.Not_included
module M: {
  type t<int>
} = {
  type t<string>
}
