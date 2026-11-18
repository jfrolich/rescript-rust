type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a) => switch x { | Int => { let g = (o: {"v": a}) => o["v"]; g({"v": y}) } }
