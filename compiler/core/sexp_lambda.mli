(* Sexp printer for Lambda IR *)

val print_lambda : Format.formatter -> Lambda.t -> unit
val print_lambda_with_locs : Format.formatter -> Lambda.t -> unit
