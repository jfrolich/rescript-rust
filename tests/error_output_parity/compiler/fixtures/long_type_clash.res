type payload = (int, string, bool, float, array<int>, array<string>) => string

let take = (value: payload) => value
let wrong: (int, string, bool, float, array<int>, array<string>) => int =
  take((a, b, c, d, e, f) => "no")
