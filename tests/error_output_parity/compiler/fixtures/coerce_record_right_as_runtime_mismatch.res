// error-output-parity: Ctype.Record_fields_mismatch(Field_runtime_name_mismatch right @as)
type source = {field: int}
type target = {@as("runtime") field: int}

let coerce = (source: source): target => (source :> target)
