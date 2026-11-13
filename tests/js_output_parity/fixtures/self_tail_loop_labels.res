@val external log: int => unit = "log"
let rec tail = (n, x) => if n { tail(false, x) } else {
  while true {
    switch x {
    | "a" => break
    | "b" => log(1)
    | "c" => log(2)
    | _ => log(3)
    }
  }
}
