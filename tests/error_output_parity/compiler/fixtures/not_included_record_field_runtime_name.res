// error-output-parity: Includecore.Field_names via @as runtime names
module M: {
  type t = {@as("a") x: int}
} = {
  type t = {@as("b") x: int}
}
