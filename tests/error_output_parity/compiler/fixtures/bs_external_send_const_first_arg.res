// error-output-parity: Ast_external_process @send rejects const first argument.
@send external send: (@as("x") _, int) => int = "send"
