// error-output-parity: Typecore.Uncurried_arity_mismatch annotated method-send
type box = {"add": (int, int) => int}

let result = (box: box) => box["add"](1)
