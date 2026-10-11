// error-output-parity: Ast_derive_js_mapper rejects unsupported jsConverter configs.
@deriving({jsConverter: {x: true}}) type t = A | B
