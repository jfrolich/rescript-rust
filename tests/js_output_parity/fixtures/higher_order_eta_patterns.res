type unary<'a, 'b> = 'a => 'b

type binary<'a, 'b, 'c> = ('a, 'b) => 'c

type runner<'a, 'b> = {run: unary<'a, 'b>}

let etaUnary = fn => value => fn(value)

let etaBinary = fn => (left, right) => fn(left, right)

let etaNested = fn => {
  let inner = value => fn(value)
  inner
}

let etaFromRecord = record => value => record.run(value)

let etaFromObject = objectValue => value => objectValue["run"](value)

let useUnary = (fn: unary<int, int>, value) => etaUnary(fn)(value)

let useBinary = (fn: binary<int, int, int>, left, right) =>
  etaBinary(fn)(left, right)

let allValues = {
  let recordRunner = {run: value => value + 1}
  let objectRunner = {"run": value => value + 2}
  (
    useUnary(value => value + 3, 4),
    useBinary((left, right) => left + right, 5, 6),
    etaNested(value => value * 2)(7),
    etaFromRecord(recordRunner)(8),
    etaFromObject(objectRunner)(9),
  )
}
