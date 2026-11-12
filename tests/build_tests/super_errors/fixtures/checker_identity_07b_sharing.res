// CHECKER_REDESIGN.md I.2.3, fixture 07b.
type myint = int
let takesMyInt = (x: myint) => ignore(x)
let dup = a => { ignore(a + 1); (a, a) }
let two = (1, 2)
let h = q => { ignore(q == dup(1)); let (a, _) = q; takesMyInt(a); q }
let k = q => { ignore(q == two); let (a, _) = q; takesMyInt(a); q }
let observed = (h, k)
let _: string = observed
