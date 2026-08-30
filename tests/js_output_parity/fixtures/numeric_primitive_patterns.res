@inline(never)
let checkedDiv = (left, right) => left / right

@inline(never)
let checkedMod = (left, right) => Int.mod(left, right)

let bitwiseOps = value => (
  Int.bitwiseAnd(value, 0xff),
  Int.bitwiseOr(value, 0x0f),
  Int.bitwiseXor(value, 0xaa),
  Int.shiftLeft(value, 3),
  Int.shiftRightUnsigned(value, 1),
  Int.shiftRight(value, 1),
)

let overflowOps = value => {
  let maxInt = 2147483647
  let minInt = -2147483648
  (
    maxInt + value,
    minInt - value,
    maxInt + maxInt + minInt,
    Int.bitwiseOr(maxInt + value, 0),
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
  Int.bitwiseXor(
    Int.bitwiseOr(Int.shiftLeft(hash, 5), Int.shiftRightUnsigned(hash, 27)),
    codePoint,
  )

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
  Float.toInt(3.8),
  Int.toFloat(7),
  hashString("output"),
)
