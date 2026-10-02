// A let pattern constraint reusing an outer type variable is linked by the
// pattern force; a mismatch is reported as Typetexp.Type_mismatch.
let f = (x: 'a) => {
  let (y: option<'a>) = x
  y
}
