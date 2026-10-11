// error-output-parity: Ast_external_process @module rejects payload-bearing @new.
type t

@module @new("Thing") external make: int => t = "M"
