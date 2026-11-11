// g0 and g1 are instances of f's type and share its `~l0` label block: 396 words, printed.
module M: {
  let v: string
} = {
  let f: (~l0: int) => int = %raw(`0`)
  let g0 = f
  let g1 = f
  let y = #a
  let v = 1
}
