// error-output-parity: Ast_derive_projector rejects accessors for inline-record variant constructors in signatures.
@deriving(accessors)
type t = A({x: int})
