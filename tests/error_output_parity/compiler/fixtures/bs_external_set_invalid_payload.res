// error-output-parity: Ast_external_process invalid @set payload.
type t

@set(1) external f: (t, int) => unit = "x"
