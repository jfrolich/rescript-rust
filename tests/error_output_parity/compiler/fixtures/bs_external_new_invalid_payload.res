// error-output-parity: Ast_external_process invalid @new payload.
type t

@new(1) external make: int => t = "Thing"
