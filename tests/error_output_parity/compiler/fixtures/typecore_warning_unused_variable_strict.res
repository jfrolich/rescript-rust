// error-output-parity: Typecore emits warning 27 for unused strict pattern variables.
let value = pair =>
  switch pair {
  | (used, unused) => used
  }
