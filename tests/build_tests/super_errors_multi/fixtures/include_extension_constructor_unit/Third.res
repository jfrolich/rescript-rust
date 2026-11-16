let x = Main.E(2)

let f = x =>
  switch x {
  | Main.E(n) => n
  | _ => 0
  }

let c: Main.t = Main.C
