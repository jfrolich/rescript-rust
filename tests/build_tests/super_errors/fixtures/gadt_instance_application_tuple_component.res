type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a) => switch x { | Int => { let g = (p: (a, int)) => { let (z, _) = p; z }; g((y, 1)) } }
