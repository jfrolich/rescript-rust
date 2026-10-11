// error-output-parity: Includecore.Arity via Typemod.Not_included
module M: {
  type t<'a>
} = {
  type t<'a, 'b>
}
