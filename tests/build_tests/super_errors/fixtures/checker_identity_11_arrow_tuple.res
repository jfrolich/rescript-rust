// CHECKER_REDESIGN.md I.2.3, fixture 11.
type myint = int
let takesMyInt = (x: myint) => ignore(x)
type cb = int => unit
type pair = (int, int)
let plainF = (f: int => unit) => ignore(f)
let takesCb = (f: cb) => ignore(f)
let plainPair = (p: (int, int)) => ignore(p)
let takesPair = (p: pair) => ignore(p)
let g = f => { plainF(f); takesCb(f); f }
let h = p => { plainPair(p); takesPair(p); p }
let observed = (g, h)
let _: string = observed
