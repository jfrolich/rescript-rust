// error-output-parity: explicit polymorphic field type has no inline record context
type t = {f: 'a. ({y: int}) => int}
