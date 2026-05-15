%%raw(`
function outputParityUseModule(moduleValue) {
  return moduleValue.compare(3, 1)
}
`)

module Numbers = {
  let label = "numbers"
  let add = (left, right) => left + right
  let length = values => values->Array.length
}

let {add, length: len, label} = module(Numbers)

let moduleRecordUse = values => add(len(values), String.length(label))

let localModuleRecordUse = values => {
  module Local = {
    let offset = 10
    let length = values => values->Array.length + offset
    let describe = value => "local:" ++ Int.toString(value)
  }

  let {length, describe} = module(Local)
  describe(length(values))
}

%%private(let {add: privateAdd, length: privateLength} = module(Numbers))

let privateModuleRecordUse = values => privateAdd(privateLength(values), 4)

module type OrderedType = {
  type t
  let compare: (t, t) => int
}

module IntOrder = {
  type t = int
  let compare = (left, right) => left - right
}

module ReverseIntOrder = {
  type t = int
  let compare = (left, right) => right - left
}

@val external useModuleExternal: module(OrderedType) => int = "outputParityUseModule"

let externalModuleValue = useModuleExternal(module(IntOrder))

type intOrder = module(OrderedType with type t = int)

let identityModule = (value: intOrder) => value

let returnedModuleValue = {
  let module(Order: OrderedType with type t = int) = identityModule(module(ReverseIntOrder))
  Order.compare(1, 3)
}

let compareWithModuleParam = (module(Order: OrderedType with type t = int), left, right) =>
  Order.compare(left, right)

module type IntOrderType = module type of IntOrder

let useModuleTypeOf = (value: module(IntOrderType)) => {
  let module(Order: IntOrderType) = value
  Order.compare(9, 4)
}

let allValues = (
  moduleRecordUse([1, 2, 3]),
  localModuleRecordUse([1, 2]),
  privateModuleRecordUse([1]),
  externalModuleValue,
  returnedModuleValue,
  compareWithModuleParam(module(IntOrder), 7, 2),
  useModuleTypeOf(module(IntOrder)),
)
