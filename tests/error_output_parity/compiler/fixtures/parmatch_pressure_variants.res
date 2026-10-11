let f = x => switch x { | #A => 1 | #B => 2 }
let g = (#A | #B) => 1
let h = x => { let #C(y) = x; y }
let k = (x, y) => switch (x, y) { | (#A, _) => 1 | (_, #B) => 2 }
let m = x => switch x { | #A => 1 | _ => 2 }
let n = (x: [< #A | #B]) => switch x { | #A => 1 }
let o = (x: [> #A]) => switch x { | #A => 1 | #Z => 3 }
let p = x => switch x { | Some(#A) => 1 | Some(#B) | None => 2 }
