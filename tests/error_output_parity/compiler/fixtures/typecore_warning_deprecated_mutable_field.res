// error-output-parity: Warning 3 for mutating a field marked @deprecated_mutable.
@@warning("+3-32-34")

type t = {
  @deprecated_mutable("use setX")
  mutable x: int,
}

let value = {x: 1}
value.x = 2
