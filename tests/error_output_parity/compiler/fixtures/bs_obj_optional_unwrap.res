// error-output-parity: Ast_external_process.process_obj rejects @unwrap optional labels.
@obj external make: (~x: @unwrap [#A(int)]=?) => _ = ""
