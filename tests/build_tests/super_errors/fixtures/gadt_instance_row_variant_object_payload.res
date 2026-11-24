type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, v: [> #A({.."g": int})]) =>
  switch x {
  | Int => #A({"g": y}) === v
  }
