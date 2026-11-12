// CHECKER_REDESIGN.md I.2.3, fixture 06.
type myint = int
let takesMyInt = (x: myint) => ignore(x)
type r = {n: int, m: int}
let f = (v: r) => { let k1 = v.n; let k2 = v.n; takesMyInt(k1); (k1, k2) }
let _: string = f
