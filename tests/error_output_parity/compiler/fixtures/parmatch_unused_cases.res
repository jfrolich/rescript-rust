type t = A | B(int) | C({x: int, y: string})
let g1 = x => switch x { | A => 1 | B(_) => 2 | C({x: 1}) => 3 | C(_) => 4 | A => 5 }
let g2 = x => switch x { | A | A => 1 | _ => 2 }
let g3 = (x: [#a | #b]) => switch x { | #a => 1 | #b => 2 | #a => 3 }
let g4 = x => switch x { | #a => 1 | #b => 2 }
exception E(int)
let g5 = x => switch x { | exception E(1) => 1 | 1 => 2 | _ => 3 }
let g6 = (x: exn) => switch x { | E(_) => 1 | Not_found => 2 }
let g7 = (d: dict<int>) => switch d { | dict{"a": 1} => 1 | dict{"b": 2} => 2 | _ => 3 }
type rr = {p: int, q: int}
let g8 = (x: rr) => switch x { | {p: 1} => 1 | {q: 2} => 2 | {p: 1, q: 2} => 3 | _ => 4 }
let g9 = (x: (int, int)) => switch x { | (1, _) | (_, 1) => 1 | (1, 1) => 2 | _ => 3 }
let g10 = x => switch x { | Some(true) => 1 | Some(false) => 2 | None => 3 | Some(_) => 4 }
let g11 = (x: string) => switch x { | "a" | "b" | "a" => 1 | _ => 2 }
let g12 = (x: option<t>) => switch x { | Some(A | B(_)) => 1 | None => 2 }
type ext = ..
type ext += X | Y
let g13 = (x: ext) => switch x { | X => 1 | Y => 2 }
let g14 = (x: unit) => switch x { | () => 1 | () => 2 }
