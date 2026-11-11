// The module types of this mismatch take 401 words: they are elided.
module M: {
  let o0: option<int>
  let f: (~k0: int) => int
  let v: string
} = {
  let o0: option<int> = %raw(`0`)
  let f: (~k0: int) => int = %raw(`0`)
  let v = 1
}
