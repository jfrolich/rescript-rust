// An untagged switch in a self-recursive function, which is compiled as a
// loop: the dispatch plan is printed with the loop's jumps.
@unboxed type rec t = | @as(null) Nil | Num(float) | S(string)
let rec loop = (x: t, acc) =>
  switch x {
  | Nil => acc
  | Num(f) => loop(Nil, acc +. f)
  | S(_) => loop(Num(1.), acc)
  }
let rec loop2 = (x: t, acc) =>
  switch x {
  | Num(f) => loop2(S("a"), acc +. f)
  | S(s) => s == "" ? acc : loop2(Nil, acc)
  | Nil => acc
  }
