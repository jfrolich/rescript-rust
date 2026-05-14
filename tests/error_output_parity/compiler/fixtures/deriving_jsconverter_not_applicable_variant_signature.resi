// error-output-parity: Ast_derive_js_mapper warns when jsConverter does not apply to regular variants in signatures.
@deriving(jsConverter) type t = A | B
