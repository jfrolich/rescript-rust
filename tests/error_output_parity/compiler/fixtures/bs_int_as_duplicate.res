// error-output-parity: Ast_attributes.iter_process_bs_int_as duplicate @as payloads.
@val external f: (@int [#a | @as(1) @as(2) #b]) => unit = "f"
