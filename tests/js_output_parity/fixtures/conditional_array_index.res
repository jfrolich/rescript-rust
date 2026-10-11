let f = (data: array<float>, i, top) => {
  let v = data[i * 2 + (top ? 1 : 0)]->Option.getOr(0.)
  top ? Math.max(0., v) : v
}
