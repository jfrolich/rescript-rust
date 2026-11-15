exception E(int)
let f = x => {
  exception L = E
  switch x {
  | L(n) => n
  | _ => 0
  }
}
