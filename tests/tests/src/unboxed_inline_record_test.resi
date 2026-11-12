@unboxed type t = Many({a: string, b: int})
@unboxed type one = One({a: string})
@unboxed type withOptional = WithOptional({a?: int, b: string})
@unboxed type mut = Mut({mutable count: int, label: string})

let make: (string, int) => t
let getA: t => string
let getB: t => int
let bump: t => t
let makeOne: string => one
let getOne: one => string
let makeWithOptional: (~a: int=?, string) => withOptional
let optionalA: withOptional => int
let makeMut: string => mut
let incr: mut => int
