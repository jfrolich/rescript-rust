// error-output-parity: for-await loops must use `of`, not `in`.
let run = async () => {
  for await item in 0 to 1 {
    ()
  }
}
