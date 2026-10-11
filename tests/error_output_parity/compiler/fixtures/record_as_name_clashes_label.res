// error-output-parity: check_duplicated_labels: an @as name clashes with an earlier label.
type t = {x: int, @as("x") y: string}
