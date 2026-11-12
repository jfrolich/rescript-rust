// CHECKER_REDESIGN.md I.2.3, fixture 09.
type myint = int
let takesMyInt = (x: myint) => ignore(x)
type phantom<'a> = int
let takesP = (x: phantom<'a>, y: 'a) => { ignore(x); ignore(y) }
let x = 1
let h = (a, w) => { ignore(a == x); takesP(a, w); a }
let _: string = h
