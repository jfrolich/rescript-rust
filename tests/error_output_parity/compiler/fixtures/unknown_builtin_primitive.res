// error-output-parity: Translcore.Unknown_builtin_primitive
external unknown: int => int = "%unknown_builtin"

let value = unknown(1)
