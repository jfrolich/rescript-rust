// error-output-parity: Ast_derive_abstract rejects combining abstract with other deriving actions.
@deriving({abstract: light, accessors: true})
type t = {x: int}
