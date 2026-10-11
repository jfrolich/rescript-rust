// Externals below the top level are validated like OCaml's builtin mapper.
let f = () => {
  module N = {
    @get external mk: (int, int) => int = "x"
  }
  1
}
