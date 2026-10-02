// Value descriptions in inclusion errors print their type with tree_of_type_scheme.
@@warning("+3-32-34")

module M: {
  external x: int => int = "%identity"
} = {
  @deprecated()
  external x: int => {..} = "%identity"
}
