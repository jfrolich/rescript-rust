// error-output-parity: Ast_attributes reports Flow parse errors for invalid @as(json`...`) payloads.
@val external f: (@as(json`{`) _) => int = "f"
