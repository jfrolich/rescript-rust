// error-output-parity: Ast_derive_projector rejects accessors for inline-record variant constructors.
@deriving(accessors)
type t = A({x: int})
