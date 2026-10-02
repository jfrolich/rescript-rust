// error-output-parity: check_duplicated_labels: two @as names clash inside an inline record.
type u = A({@as("q") m: int, @as("q") n: int})
