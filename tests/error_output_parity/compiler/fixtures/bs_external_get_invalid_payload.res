// error-output-parity: Ast_external_process invalid @get payload.
type t

@get(1) external f: t => int = "x"
