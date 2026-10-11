// error-output-parity: Ast_external_process rejects underscore optional arguments.
@val external f: (~x: _=?) => unit = "f"
