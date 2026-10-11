// error-output-parity: parser normalize_for_of_pattern reports destructuring pattern location.

for (a, b) of [(1, 2)] {
  ignore(a)
  ignore(b)
}
