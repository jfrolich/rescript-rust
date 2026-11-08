// error-output-parity: Typecore.Label_mismatch wider than the margin
type recordTypeWithAVeryLongNameThatDoesNotFitNumberOne = {x: int}
type recordTypeWithAVeryLongNameThatDoesNotFitNumberTwo = {y: int}
let _ = {x: 1, y: 2}
