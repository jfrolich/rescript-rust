// error-output-parity: Ast_external_process @module import attributes require string values.
@module({from: "pkg", with: {type_: 1}}) external x: int = "x"
