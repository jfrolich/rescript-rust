module X: {
  type t = ..
  let f: t => int
} = {
  type t = ..
  type t += A(int)
  type t += private B = A
  let f = x =>
    switch x {
    | B(n) => n
    | _ => 0
    }
}
