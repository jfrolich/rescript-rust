type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a) => switch x { | Int => { let g = (p: [#V(a)]) => switch p { | #V(z) => z }; g(#V(y)) } }
