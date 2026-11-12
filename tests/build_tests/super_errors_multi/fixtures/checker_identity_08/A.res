// CHECKER_REDESIGN.md I.2.3, fixture 8.
type myint = int
let takesMyInt = (x: myint) => ignore(x)
let x = 1
let dup = a => { ignore(a + 1); (a, a) }
let two = (1, 2)
