// Ctype.closed_extension_constructor reports the free row variable and
// explain_unbound prints the argument containing it.
type t = ..
type t += A({..}) | B([> #x])
exception C({x: {..}})
