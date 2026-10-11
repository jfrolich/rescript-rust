module M: {external x: int => int = "%identity"} = {
  let x = (y: int) => y
}
