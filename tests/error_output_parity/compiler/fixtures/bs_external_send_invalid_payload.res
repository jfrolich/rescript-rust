// error-output-parity: Ast_external_process invalid @send payload.
type t

@send(1) external f: (t, int) => int = "f"
