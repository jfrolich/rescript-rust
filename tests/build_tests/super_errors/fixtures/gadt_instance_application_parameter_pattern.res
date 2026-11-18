type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a) => switch x { | Int => { let g = ((z: a, _)) => z; g((y, 1)) } }
