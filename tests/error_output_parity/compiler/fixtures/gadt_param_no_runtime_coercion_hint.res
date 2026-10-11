type rec kind<_> =
  | Float: kind<float>
@val external add: (@ignore kind<[< #a | #b]>, int) => int = "add"
let _ = add(Float, 3)
