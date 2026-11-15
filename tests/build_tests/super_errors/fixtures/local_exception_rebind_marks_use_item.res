exception E(int)
module X: {
  let f: exn => int
} = {
  exception L = E
  exception M = L
  let f = x =>
    switch x {
    | L(n) => n
    | M(_) => 1
    | _ => 0
    }
}
