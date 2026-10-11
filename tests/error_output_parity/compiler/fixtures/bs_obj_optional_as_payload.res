// error-output-parity: Ast_external_process.process_obj warns for unused @as optional labels.
@obj external make: (~x: @as("x") int=?) => _ = ""
