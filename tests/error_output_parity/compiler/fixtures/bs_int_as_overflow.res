// error-output-parity: Ast_payload.is_single_int oversized @as payloads.
@val external f: (@int [#a | @as(999999999999999999999999999999) #b]) => unit = "f"
