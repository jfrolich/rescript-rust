// error-output-parity: record field doc comments must appear before the field.
type t = {
  field: string, /** here */
}
