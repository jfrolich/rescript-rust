// error-output-parity: delayed unused warnings are not reported when typing fails
let f = () => {
  let unused = 1
  2
}
include {
  let helper = 1
}
let bad: int = "not an int"
