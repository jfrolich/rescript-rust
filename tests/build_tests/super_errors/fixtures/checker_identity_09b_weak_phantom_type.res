// CHECKER_REDESIGN.md I.2.3, fixture 9b: accepted despite the weak phantom.
type phantom<'a> = int
let takesP = (x: phantom<'a>, y: array<'a>) => { ignore(x); ignore(y) }
let cell = ref(None)
cell := Some(1)
takesP(Option.getOr(cell.contents, 0), [])
let _: string = cell
