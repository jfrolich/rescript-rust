// Externals below the top level are validated like OCaml's builtin mapper.
module type S = {
  @get external mk: (int, int) => int = "x"
}
