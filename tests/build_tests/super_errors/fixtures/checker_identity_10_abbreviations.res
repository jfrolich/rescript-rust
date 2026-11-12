// CHECKER_REDESIGN.md I.2.3, fixture 10.
type myint = int
let takesMyInt = (x: myint) => ignore(x)
type a = int
type b = int
let takesA = (x: a) => ignore(x)
let takesB = (x: b) => ignore(x)
let g = v => { takesA(v); takesB(v); v }
let h = v => { takesB(v); takesA(v); v }
let observed = (g, h)
let _: string = observed
