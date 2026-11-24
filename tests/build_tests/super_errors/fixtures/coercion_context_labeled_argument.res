let g = (~x: string) => x
let f = (o: int) => g(~x=(o :> int))
