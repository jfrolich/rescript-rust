type rec t<_> = Int: t<int> | Str: t<string>
let g = x =>
  switch Obj.magic(x) {
  | Int => 1
  | (1, 2) => 2
  | _ => 3
  }
