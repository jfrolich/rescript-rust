type action = A({y: int}) | B
let f = (action: action) =>
  switch action {
  | A(_: 'a) | B => 1
  }
