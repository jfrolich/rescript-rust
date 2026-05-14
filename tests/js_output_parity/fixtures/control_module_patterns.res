type orderStatus = Open | Paid | Cancelled
type order = {id: int, status: orderStatus, total: int}

let scanOrders = (orders: array<order>) => {
  let matchId = ref(None)

  for order of orders {
    switch order.status {
    | Cancelled | Paid => continue
    | Open =>
      if order.total >= 500 {
        matchId := Some(order.id)
        break
      }
    }
  }

  matchId.contents
}

let countWildcard = (values: array<int>) => {
  let count = ref(0)
  for _ of values {
    count := count.contents + 1
  }
  count.contents
}

let asyncSource: AsyncIterable.t<int> = %raw(`(async function* () {
  yield 1
  yield 2
  yield 3
  yield 4
})()`)

let collectAsync = async source => {
  let seen = []
  for await value of source {
    switch value {
    | 1 => continue
    | 4 => break
    | _ => seen->Array.push(value)
    }
  }
  seen
}

let rangeTotals = limit => {
  let up = ref(0)
  for index in 0 to limit {
    up := up.contents + index
  }

  let down = ref(0)
  for index in limit downto 0 {
    down := down.contents + index
  }

  (up.contents, down.contents)
}

let rec even = value =>
  switch value {
  | 0 => true
  | n => odd(n - 1)
  }
and odd = value =>
  switch value {
  | 0 => false
  | n => even(n - 1)
  }

module rec EvenModule: {
  let even: int => bool
  let seed: unit => int
} = {
  let even = value =>
    if value == 0 {
      true
    } else {
      OddModule.odd(value - 1)
    }
  let seed = () => OddModule.seed() + 1
}
and OddModule: {
  let odd: int => bool
  let seed: unit => int
} = {
  let odd = value =>
    if value == 0 {
      false
    } else {
      EvenModule.even(value - 1)
    }
  let seed = () => 40
}

module type Stepper = {
  let step: int => int
}

module MakeStepper = (Input: Stepper) => {
  let run = value => Input.step(Input.step(value))
}

module DoubleStep = MakeStepper({
  let step = value => value + 1
})

let lazyPair = {
  let left = Lazy.make(() => DoubleStep.run(EvenModule.seed()))
  let right = Lazy.make(() => if OddModule.odd(3) { "odd" } else { "even" })
  (Lazy.get(left), Lazy.get(right))
}

let directiveFn = @directive("'use memo'") name => "hello " ++ name

type event = ..
type event += Inline({code: int, label?: string})
type event += Tuple(int, string)
type event += Single(string)

exception Payload({code: int, label?: string})
exception Pair(int, string)

let eventValue = event =>
  switch event {
  | Inline({code, label}) => code + String.length(label)
  | Inline({code}) => code
  | Tuple(code, label) => code + String.length(label)
  | Single(label) => String.length(label)
  | _ => 0
  }

let exceptionValue = run =>
  try {
    run()
    0
  } catch {
  | Payload({code, label}) => code + String.length(label)
  | Payload({code}) => code
  | Pair(code, label) => code + String.length(label)
  | _ => -1
  }

let allValues = (
  scanOrders([
    {id: 1, status: Cancelled, total: 900},
    {id: 2, status: Open, total: 450},
    {id: 3, status: Open, total: 650},
  ]),
  countWildcard([1, 2, 3]),
  collectAsync(asyncSource),
  rangeTotals(4),
  even(6),
  DoubleStep.run(1),
  lazyPair,
  directiveFn("parity"),
  eventValue(Inline({code: 10, label: "x"})),
  exceptionValue(() => throw(Pair(4, "xy"))),
)
