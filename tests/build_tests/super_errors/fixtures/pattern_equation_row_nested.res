type rec t<_> = A: t<([#a], int)>
let f = (x: t<([#a | #b], int)>) => switch x { | A => 0 }
