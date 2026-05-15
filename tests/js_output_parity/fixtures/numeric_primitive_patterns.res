@inline(never)
let checkedDiv = (left, right) => left / right

@inline(never)
let checkedMod = (left, right) => mod(left, right)

let bitwiseOps = value => (
  land(value, 0xff),
  lor(value, 0x0f),
  lxor(value, 0xaa),
  lsl(value, 3),
  lsr(value, 1),
  asr(value, 1),
)

let overflowOps = value => {
  let maxInt = 2147483647
  let minInt = -2147483648
  (
    maxInt + value,
    minInt - value,
    maxInt + maxInt + minInt,
    lor(maxInt + value, 0),
  )
}

let floatOps = (left, right) => (
  left +. right,
  left -. right,
  left *. right,
  left /. right,
)

let compareOps = (left, right) => (
  left < right,
  left <= right,
  left > right,
  left >= right,
  left == right,
  left !== right,
)

let assertionValue = value => {
  assert(value > 0)
  value
}

let hashStep = (hash, codePoint) =>
  lxor(lor(lsl(hash, 5), lsr(hash, 27)), codePoint)

let hashString = value => {
  let hash = ref(0)
  for index in 0 to String.length(value) - 1 {
    hash := hashStep(hash.contents, String.codePointAt(value, index)->Option.getUnsafe)
  }
  hash.contents
}

let allValues = (
  checkedDiv(7, 2),
  checkedMod(7, 3),
  bitwiseOps(0x1234),
  overflowOps(1),
  floatOps(7.5, 2.5),
  compareOps(3, 4),
  assertionValue(1),
  int_of_float(3.8),
  float_of_int(7),
  hashString("output"),
)
