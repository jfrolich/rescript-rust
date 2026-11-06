// A variance mismatch prints its module types in the usual box.
module N: {
  type t<+'a>
} = {
  type t<'a> = 'a => unit
}
