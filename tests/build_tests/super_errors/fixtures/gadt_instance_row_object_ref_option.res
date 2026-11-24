type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, r: ref<option<{.."f": int}>>) =>
  switch x {
  | Int => r := Some({"f": y})
  }
