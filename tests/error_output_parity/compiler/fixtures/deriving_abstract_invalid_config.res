// error-output-parity: Ast_derive_abstract rejects unsupported abstract configs.
@deriving({abstract: unknown}) type t = {x: int}
