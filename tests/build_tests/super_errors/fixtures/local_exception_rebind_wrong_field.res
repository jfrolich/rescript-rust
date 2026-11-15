exception E({a: int, b: string})
let f = x => {
  exception L = E
  switch x {
  | L({c}) => c
  | _ => 0
  }
}
