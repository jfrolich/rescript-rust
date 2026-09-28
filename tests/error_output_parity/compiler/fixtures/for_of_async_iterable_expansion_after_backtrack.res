// error-output-parity: a failed for...of keeps the iterable expansion made before backtracking.
let f = (x: AsyncIterable.t<int>) => {
  for _ of x {
    ()
  }
}
