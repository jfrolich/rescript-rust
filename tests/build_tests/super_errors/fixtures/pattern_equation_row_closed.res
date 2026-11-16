type rec t<_> = A: t<[#a]>
let f = (x: t<[#a | #b]>) => switch x { | A => 0 }
