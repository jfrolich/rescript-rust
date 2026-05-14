// error-output-parity: Typecore.Invalid_for_loop_index
for (x, y) in 0 to 10 {
  ignore((x, y))
}
