// CHECKER_REDESIGN.md I.2.3, fixture 07.
type myint = int
let takesMyInt = (x: myint) => ignore(x)
let pairConst = (1, 2)
let h = q => { ignore(q == pairConst); let (a, _) = q; takesMyInt(a); q }
let observed = (h, pairConst)
let _: string = observed
