type rec t<_> = Int: t<int>
let h = (o: option<int>) => switch o { | Some(n) => n | None => 0 }
let f = (type a, x: t<a>, y: a) => switch x { | Int => { let g = (z: a) => z; g(y) } }
