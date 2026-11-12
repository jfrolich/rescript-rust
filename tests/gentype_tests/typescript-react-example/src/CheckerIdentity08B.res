@genType
let g = a => { ignore(a == CheckerIdentity08A.x); CheckerIdentity08A.takesMyInt(a); a }
@genType
let h = q => { ignore(q == CheckerIdentity08A.dup(1)); let (a, _) = q; CheckerIdentity08A.takesMyInt(a); q }
@genType
let k = q => { ignore(q == CheckerIdentity08A.two); let (a, _) = q; CheckerIdentity08A.takesMyInt(a); q }
