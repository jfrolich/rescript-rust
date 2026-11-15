exception E(int)
let f = x => {
  exception L = E
  exception M = L
  switch x {
  | L(n) => n
  | _ => 0
  }
}
