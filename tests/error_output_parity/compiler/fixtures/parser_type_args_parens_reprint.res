// error-output-parity: the angle-bracket hint reprints the type arguments
type user = {name: string}
type t = option({...user, "age": int}, array<int>)
