// error-output-parity: Ast_external_process @variadic rejects optional last argument.
@variadic external f: (~xs: array<int>=?) => unit = "f"
