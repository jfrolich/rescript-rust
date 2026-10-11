// for-await with `in` and a missing direction keyword.
let run = async () => {
  for await item in 1n  1 {
    ()
  }
}
