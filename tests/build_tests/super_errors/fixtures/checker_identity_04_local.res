// CHECKER_REDESIGN.md I.2.3, fixture 04.
type myint = int
let takesMyInt = (x: myint) => ignore(x)
let f = a => { let b = a; ignore(b + 1); takesMyInt(b); a }
let _: string = f
