type t = A | B | C
let f = x => switch x { | A => 1 | B => 2 | A => 3 | C => 4 }
let g = (x: t) => switch x { | A => 1 }
let h = x => switch x { | Some(1) => 1 | None => 2 }
