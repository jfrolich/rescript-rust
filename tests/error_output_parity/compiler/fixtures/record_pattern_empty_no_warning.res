// error-output-parity: an empty record pattern has no missing-label warning
type x = {name: string, age: int}
let f = (x: x) => {
  let {} = x
  1
}
let y: int = "no"
