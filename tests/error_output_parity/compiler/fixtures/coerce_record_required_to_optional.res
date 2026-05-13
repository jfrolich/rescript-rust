// error-output-parity: Ctype.Record_fields_mismatch(Optional_mismatch required to optional)
type source = {field: int}
type target = {field?: int}

let coerce = (source: source): target => (source :> target)
