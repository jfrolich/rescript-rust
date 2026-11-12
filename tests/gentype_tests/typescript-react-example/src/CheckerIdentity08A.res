// CHECKER_REDESIGN.md I.2.3, fixture 8.
@genType
type myint = int
@genType
let takesMyInt = (x: myint) => ignore(x)
@genType
let x = 1
@genType
let dup = a => { ignore(a + 1); (a, a) }
@genType
let two = (1, 2)
