// error-output-parity: Ast_attributes.iter_process_bs_string_as duplicate @as payloads.
@val external f: (@string [#a | @as("a") @as("b") #b]) => unit = "f"
