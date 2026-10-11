// error-output-parity: Typecore emits warning 21 for statements after break.
for i in 0 to 1 {
  break
  ignore(i)
}
