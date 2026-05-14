// error-output-parity: Ast_external_process @set_index requires empty primitive name.
@set_index external set: (int, int, int) => unit = "set"
