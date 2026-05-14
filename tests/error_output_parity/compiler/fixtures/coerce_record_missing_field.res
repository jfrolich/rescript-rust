// error-output-parity: Ctype.Record_fields_mismatch(Field_missing)
type source = {a: int}
type target = {a: int, b: int}

let coerce = (source: source): target => (source :> target)
