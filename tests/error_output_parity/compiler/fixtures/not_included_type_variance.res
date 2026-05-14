// error-output-parity: Includecore.Variance via Typemod.Not_included
module M: {
  type t<+'a>
} = {
  type t<'a>
}
