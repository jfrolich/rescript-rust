- Type checker: unification links an expanded abbreviation to the original
  type before unifying the children, as OCaml does, so error messages print the
  same alias spelling (for example `id<id<(int, int)>>`) as the OCaml compiler.
