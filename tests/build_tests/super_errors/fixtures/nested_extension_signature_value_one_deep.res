module R = {
  type t = X
  let x: t = X
}
module S: {
  let x: int
} = R
