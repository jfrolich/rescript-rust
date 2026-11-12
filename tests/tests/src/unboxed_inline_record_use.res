// Uses the @unboxed inline-record types of Unboxed_inline_record_test through
// its interface.
module U = Unboxed_inline_record_test

let fromOther = U.Many({a: "other", b: 5})
let describeT = x =>
  switch x {
  | U.Many({a, b}) => a ++ Int.toString(b)
  }
let viaInterface = U.getA(U.make("i", 1))
let oneValue = (U.One({a})) => a
let optionalValue = (U.WithOptional({b})) => b
let mutCount = (U.Mut(r)) => r.count

module type S = {
  @unboxed type t = Many({a: string, b: int})
  let get: t => string
}

module M: S = {
  @unboxed type t = Many({a: string, b: int})
  let get = (Many(r)) => r.a
}

module F = (X: S) => {
  let b = (x: X.t) =>
    switch x {
    | X.Many({b}) => b
    }
}

module FM = F(M)

let fromModuleType = (M.Many({b})) => b
let applied = FM.b(M.Many({a: "m", b: 3}))
