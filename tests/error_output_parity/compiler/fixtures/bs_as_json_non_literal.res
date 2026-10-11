// error-output-parity: Ast_attributes rejects non-literal @as(json`...`) payloads.
@val external f: (@as(json`foo + bar`) _) => int = "f"
