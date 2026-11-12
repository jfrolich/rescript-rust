// CHECKER_REDESIGN.md I.2.3, fixture 03.
type myint = int
let takesMyInt = (x: myint) => ignore(x)
let x = 1
takesMyInt(x)
takesMyInt(x)
let observed = (x, x)
let _: string = observed
