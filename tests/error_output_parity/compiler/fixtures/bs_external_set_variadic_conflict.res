// error-output-parity: Ast_external_process @set rejects conflicting @variadic.
@set @variadic external set: (int, int) => unit = "value"
