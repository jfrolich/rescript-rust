module type S = {
  let @send x: int
}

module Make = (U: S) => {
  include U
}
