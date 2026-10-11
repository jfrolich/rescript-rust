// Ctype.copy keeps the row-variable marker for the whole instance, so both
// occurrences of the constrained row become one node and print as an alias.
let g = (x: [< #a | #b]) => x
let v: int = g
