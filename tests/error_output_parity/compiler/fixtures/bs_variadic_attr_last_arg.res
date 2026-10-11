// error-output-parity: Ast_external_process @variadic rejects FFI-attributed last arguments.
@variadic external f: (@int [#A]) => unit = "f"
