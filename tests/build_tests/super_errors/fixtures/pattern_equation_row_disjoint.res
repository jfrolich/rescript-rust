type rec t<_> = A: t<[#a]>
let f = (x: t<[#b]>) => switch x { | A => 0 }
