// for-loop recovery: a missing `to`/`downto` reports the unexpected token.
for x in 0 "10" to {
  Console.log(x)
}
