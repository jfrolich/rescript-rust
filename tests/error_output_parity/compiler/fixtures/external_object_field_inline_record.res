// error-output-parity: object field types in an external arrow parameter have no inline record context.
external c: (~j: {"a": int, "w": {e}}=?) => int = "c"
