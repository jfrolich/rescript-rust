// CHECKER_REDESIGN.md I.2.3, fixture 02.
type myint = int
let takesMyInt = (x: myint) => ignore(x)
let f = (a: int) => { takesMyInt(a); a }
let _: string = f
