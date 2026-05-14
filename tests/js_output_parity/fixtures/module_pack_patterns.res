module type Counter = {
  type t
  let zero: t
  let add: (t, t) => t
  let show: t => string
}

module IntCounter = {
  type t = int
  let zero = 0
  let add = (left, right) => left + right
  let show = value => Int.toString(value)
}

type intCounter = module(Counter with type t = int)

let packedInt: intCounter = module(IntCounter)

module FromPacked = unpack(packedInt)

let directUnpack = FromPacked.show(FromPacked.add(FromPacked.zero, 3))

let usePacked = (pack: intCounter) => {
  let module(C: Counter with type t = int) = pack
  C.show(C.add(C.zero, 5))
}

let makeCounter = (~offset): intCounter => {
  module Local = {
    type t = int
    let zero = offset
    let add = (left, right) => left + right
    let show = value => "local:" ++ Int.toString(value)
  }
  module(Local)
}

let useReturnedPack = {
  let module(C: Counter with type t = int) = makeCounter(~offset=10)
  C.show(C.add(C.zero, 7))
}

let packageArray = [module(IntCounter: Counter with type t = int), makeCounter(~offset=20)]

let usePackageArray = {
  let module(C: Counter with type t = int) = packageArray->Array.getUnsafe(1)
  C.show(C.add(C.zero, 4))
}

let localModuleBinding = {
  module Local = {
    let value = 40
    let format = value => "value:" ++ Int.toString(value)
  }
  module Alias = Local
  Alias.format(Alias.value + 2)
}

module MakeWithCounter = (Input: Counter with type t = int) => {
  let value = Input.show(Input.add(Input.zero, 9))
}

module Made = MakeWithCounter(FromPacked)

let allValues = (
  directUnpack,
  usePacked(packedInt),
  useReturnedPack,
  usePackageArray,
  localModuleBinding,
  Made.value,
)
