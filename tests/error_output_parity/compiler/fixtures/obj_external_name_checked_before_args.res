// error-output-parity: Ast_external_process.process_obj rejects non-empty @obj external names.
@obj external make: (@int [#a | @as(999999999999999999999999999999) #b]) => _ = "make"
