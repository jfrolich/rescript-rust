// error-output-parity: Transl_recmodule.Circular_dependency
module rec A: {
  let value: int
} = {
  let value = B.value
}
and B: {
  let value: int
} = {
  let value = A.value
}
