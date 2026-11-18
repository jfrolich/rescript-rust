type rec t<_> = Int: t<int>
let f = (type a, x: option<t<a>>, y: a) =>
  switch x {
  | Some(Int) => if true { y } else { 0 }
  | None => y
  }
