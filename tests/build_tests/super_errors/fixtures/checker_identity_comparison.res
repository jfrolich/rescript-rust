// CHECKER_REDESIGN.md I.2.4: renaming changes comparison specialization.
type color = Red | Green
type id<'a> = 'a
let takesId = (x: id<color>) => ignore(x)
let x = Red
let g = a => { ignore(a == x); takesId(a); a > Green }
let h = a => { ignore(a == x); a > Green }
