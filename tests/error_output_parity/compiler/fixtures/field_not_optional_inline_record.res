// error-output-parity: Typecore.Field_not_optional
type inline = A({nonopt: int, opt?: string})

let vi = A({nonopt: ?3, opt: ?None})
