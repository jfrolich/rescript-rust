// The name an inferred type is printed with follows the nodes unification
// links: `a` is first unified with the type of `x` (an instance of `int`),
// then that node is unified with `myint`, so `g` is `myint => myint`.
// Sharing the `int` node of `x`'s type between its uses, or giving it a
// different level, changes which node is linked and so the printed name.
type myint = int
let takesMyInt = (x: myint) => ignore(x)
let x = 1
let g = a => {
  ignore(a == x)
  takesMyInt(a)
  a
}
let h = o =>
  switch o {
  | Some(v) =>
    takesMyInt(v)
    v
  | None => x
  }
let y: int = x
let all = (g, h, y)
let _: string = all
