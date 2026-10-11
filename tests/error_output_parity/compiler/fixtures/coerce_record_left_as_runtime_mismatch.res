// error-output-parity: Ctype.Record_fields_mismatch(Field_runtime_name_mismatch left @as)
type source = {@as("runtime") field: int}
type target = {field: int}

let coerce = (source: source): target => (source :> target)
