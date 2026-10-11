module M: {external x: int => int = "%identity"} = {
  @deprecated() external x: int => int = "s"
}
