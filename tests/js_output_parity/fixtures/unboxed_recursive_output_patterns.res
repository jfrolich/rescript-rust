@unboxed type rec unknownBox = unknown = Unknown(_): unknownBox

let wrapUnknown = (value: unknown) => Some(value)

let unknownValues = [
  Unknown(3),
  Unknown("three"),
  Unknown(Some(Unknown(2))),
]

let unwrapUnknown = value =>
  switch value {
  | Unknown(_) => 1
  }

@unboxed type identityRecord = {f: 'a. 'a => 'a}

let mapPair = (record, (left, right)) => (record.f(left), record.f(right))

let identityValue = {f: value => value}

let mappedPair = mapPair(identityValue, (3, true))

type para<_> = C

@unboxed type rec nested = H(para<_>): nested

let nestedValue = H(C)

@unboxed type rec anyBox = Any('a): anyBox

let anyValues = [Any(3), Any(2), Any("x")]

let dumpAny = value =>
  switch value {
  | Any(inner) => Console.log(inner)
  }

let dumpedValues = {
  dumpAny(Any(3))
  dumpAny(Any("x"))
}

type rec recursiveTree<'a, 'b> = [
  | #A(recursiveTreeAux<int, string>)
  | #B
]
@unboxed and recursiveTreeAux<'a, 'b> = {field: recursiveTree<'a, 'b>}

let rec recursiveValue: recursiveTree<_> = #A({field: #B})

let recursiveResult =
  switch recursiveValue {
  | #A({field}) => field
  | #B => #B
  }
