// error-output-parity: Ast_external_process.process_obj warns for unused non-underscore @as labels.
@obj external make: (~x: @as("a") @as("b") int) => _ = ""
