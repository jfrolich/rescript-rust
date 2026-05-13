// error-output-parity: Typecore emits warning 35 for unused for-await-of indexes.
@val external asyncIterable: AsyncIterable.t<int> = "asyncIterable"

let run = async () => {
  for await item of asyncIterable {
    ()
  }
}
