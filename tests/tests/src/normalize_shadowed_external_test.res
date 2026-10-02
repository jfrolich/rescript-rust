// The final signature normalization (`normalize_signature` on the simplified
// signature) skips the external shadowed by the wrapper below, so its object
// row keeps the order type translation gave it.
type t
@module("node:url")
external format: (
  t,
  {
    "auth": Nullable.t<bool>,
    "fragment": Nullable.t<bool>,
  },
) => string = "format"
let format = (~auth=?, ~fragment=?, url) =>
  format(
    url,
    {
      "auth": Nullable.fromOption(auth),
      "fragment": Nullable.fromOption(fragment),
    },
  )
