// error-output-parity: Ctype.Record_fields_mismatch(Optional_mismatch optional to required)
type source = {field?: int}
type target = {field: int}

let coerce = (source: source): target => (source :> target)
