module type S = {
  @deriving(accessors) type t
  external f: @string [#a] => unit = "f"
}
