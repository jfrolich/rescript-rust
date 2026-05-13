// error-output-parity: Ast_derive_projector rejects unsupported accessors configs.
@deriving({accessors: {x: true}}) type t = {x: int}
