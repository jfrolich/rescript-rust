@inline(never)
let intCompare = (left: int, right: int) => compare(left, right)

@inline(never)
let intMin = (left: int, right: int) => min(left, right)

@inline(never)
let intMax = (left: int, right: int) => max(left, right)

@inline(never)
let floatCompare = (left: float, right: float) => compare(left, right)

@inline(never)
let floatMin = (left: float, right: float) => min(left, right)

@inline(never)
let floatMax = (left: float, right: float) => max(left, right)

@inline(never)
let stringCompare = (left: string, right: string) => compare(left, right)

@inline(never)
let stringMin = (left: string, right: string) => min(left, right)

@inline(never)
let stringMax = (left: string, right: string) => max(left, right)

@inline(never)
let boolCompare = (left: bool, right: bool) => compare(left, right)

@inline(never)
let boolMin = (left: bool, right: bool) => min(left, right)

@inline(never)
let boolMax = (left: bool, right: bool) => max(left, right)

@inline(never)
let bigintCompare = (left: bigint, right: bigint) => compare(left, right)

@inline(never)
let bigintMin = (left: bigint, right: bigint) => min(left, right)

@inline(never)
let bigintMax = (left: bigint, right: bigint) => max(left, right)

type payload = {name: string, rank: int}

@inline(never)
let objectCompare = (left: payload, right: payload) => compare(left, right)

@inline(never)
let objectMin = (left: payload, right: payload) => min(left, right)

@inline(never)
let objectMax = (left: payload, right: payload) => max(left, right)

@inline(never)
let checkedStringGet = (value, index) => String.getUnsafe(value, index)

@inline(never)
let checkedArrayGet = (values, index) => Array.get(values, index)

@inline(never)
let checkedArraySet = (values, index, value) => Array.set(values, index, value)

let payloadA = {name: "a", rank: 1}
let payloadB = {name: "b", rank: 2}

let arrayValues = [1, 2, 3]

let allValues = {
  checkedArraySet(arrayValues, 1, 9)
  (
    intCompare(4, 2),
    intMin(4, 2),
    intMax(4, 2),
    floatCompare(4.5, 2.5),
    floatMin(4.5, 2.5),
    floatMax(4.5, 2.5),
    stringCompare("beta", "alpha"),
    stringMin("beta", "alpha"),
    stringMax("beta", "alpha"),
    boolCompare(true, false),
    boolMin(true, false),
    boolMax(true, false),
    bigintCompare(4n, 2n),
    bigintMin(4n, 2n),
    bigintMax(4n, 2n),
    objectCompare(payloadA, payloadB),
    objectMin(payloadA, payloadB),
    objectMax(payloadA, payloadB),
    checkedStringGet("runtime", 2),
    checkedArrayGet(arrayValues, 1),
  )
}
