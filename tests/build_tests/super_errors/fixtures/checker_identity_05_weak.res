// CHECKER_REDESIGN.md I.2.3, fixture 05.
type myint = int
let takesMyInt = (x: myint) => ignore(x)
let r = ref(None)
let x = 1
r := Some(x)
let y = switch r.contents { | Some(v) => v | None => 0 }
takesMyInt(y)
let observed = (r, x, y)
let _: string = observed
