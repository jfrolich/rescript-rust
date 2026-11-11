// A class is imported as a module: `t` is the type of its instances,
// `make` its constructor, and the static members are values.
module Counter = %ts("./counter.ts#Counter")
let {sum} = %ts("./counter.ts")

let a = Counter.make(10.)
let b = Counter.make(1., ~step=5.)
let c = Counter.zero()

// Methods and properties are the fields of `t`. Private members are left out.
let next = a.increment(~by=2.)
let empty = c.isZero
let total = sum([a, b, c])
