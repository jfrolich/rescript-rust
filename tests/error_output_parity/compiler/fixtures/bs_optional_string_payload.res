// error-output-parity: Ast_external_process rejects payload @string optional arguments.
@val external f: (~x: @string [#A(int)]=?) => unit = "f"
