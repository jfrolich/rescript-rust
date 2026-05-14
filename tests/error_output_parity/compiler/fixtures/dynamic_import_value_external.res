// error-output-parity: raw %import external rejects non-module values.
external importValue: int => promise<int> = "%import"

let _ = importValue(1)
