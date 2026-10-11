type rec t<'a> = Int: t<int>

let f = (x: t<char>) =>
  switch x {
  | Int => 0
  }

type rec g<'a> = I: g<int> | S: g<string>
let h = (x: g<bool>) =>
  switch x {
  | I => 0
  }
