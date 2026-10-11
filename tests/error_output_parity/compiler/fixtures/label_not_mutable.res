// error-output-parity: Typecore.Label_not_mutable
type value = {x: int}

let result = {
  let record = {x: 1}
  record.x = 2
}
