let g = a => { ignore(a == A.x); A.takesMyInt(a); a }
let h = q => { ignore(q == A.dup(1)); let (a, _) = q; A.takesMyInt(a); q }
let k = q => { ignore(q == A.two); let (a, _) = q; A.takesMyInt(a); q }
let observed = (g, h, k)
let _: string = observed
