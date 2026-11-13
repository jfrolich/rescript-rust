@val external log: int => unit = "log"

// A source loop preserves the switch context inherited by its body.
let nested = x => {
  while true {
    switch x {
    | "a" => while true { break }
    | "b" => log(1)
    | "c" => log(2)
    | _ => break
    }
    break
  }
}
