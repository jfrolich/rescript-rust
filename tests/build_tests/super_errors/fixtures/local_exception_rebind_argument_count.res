exception E(int)
let f = x => {
  exception L = E
  switch x {
  | L(n, m) => n + m
  | _ => 0
  }
}
