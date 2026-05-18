module A = {
  type t = int
}

module B = {
  type t = string
}

module UseA = {
  open A
  let first: t = 1
}

module UseB = {
  open A
  let first: t = 1

  open B
  let second: t = "second"

  let pair = (first, second)
}
