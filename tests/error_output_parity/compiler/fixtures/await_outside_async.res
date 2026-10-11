// error-output-parity: bs_builtin_ppx rejects await outside async context.
let _ = await Promise.resolve(1)
