// Externals below the top level are validated like OCaml's builtin mapper.
let f = () => {
  module N = {
    external mk: int => int = ""
  }
  N.mk(1)
}
