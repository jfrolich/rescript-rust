type r = {mutable a: string}
let f = (r: r, o: int) => r.a = (o :> int)
