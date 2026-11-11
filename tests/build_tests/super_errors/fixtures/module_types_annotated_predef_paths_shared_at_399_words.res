// The literals and `None` share their predefined paths: 399 words, printed.
module M: {
  let x0: int
  let y0: string
  let o0: option<int>
  let v: string
} = {
  let x0 = 0
  let y0: string = %raw(`0`)
  let o0: option<int> = None
  let v = 1
}
