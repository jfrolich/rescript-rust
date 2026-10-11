// error-output-parity: @@config warning flags also apply to frontend PPX warnings.
@@config({flags: ["-warn-error", "+A"]})

let _ = %raw("function")
