// error-output-parity: Ast_derive_js_mapper warns when jsConverter does not apply to non-polyvariant abstract types in signatures.
@deriving(jsConverter) type t = int
