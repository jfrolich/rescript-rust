// CHECKER_REDESIGN.md I.2.3, fixture 06b.
type myint = int
let takesMyInt = (x: myint) => ignore(x)
type r = {n: int, m: int}
let mk = a => { let v = {n: a, m: 0}; takesMyInt(a); v }
let _: string = mk
