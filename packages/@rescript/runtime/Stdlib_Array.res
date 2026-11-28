type t<'a> = array<'a>
type arrayLike<+'a>

@pure @new external makeUninitializedUnsafe: int => array<'a> = "Array"
@pure @set external truncateToLengthUnsafe: (array<'a>, int) => unit = "length"

@pure
external getUnsafe: (array<'a>, int) => 'a = "%array_unsafe_get"

@mutates
external setUnsafe: (array<'a>, int, 'a) => unit = "%array_unsafe_set"

@pure
external asIterable: array<'a> => Stdlib_Iterable.t<'a> = "%identity"

@val @pure
external fromIterable: Stdlib_Iterable.t<'a> => array<'a> = "Array.from"

@pure @val external fromArrayLike: arrayLike<'a> => array<'a> = "Array.from"

@val @pure
external fromArrayLikeWithMap: (arrayLike<'a>, 'a => 'b) => array<'b> = "Array.from"

@pure @val external fromString: string => array<string> = "Array.from"

@mutates @send external fill: (array<'a>, 'a, ~start: int=?, ~end: int=?) => unit = "fill"

let make = (~length, x) =>
  if length <= 0 {
    []
  } else {
    let arr = makeUninitializedUnsafe(length)
    arr->fill(x)
    arr
  }

let fromInitializer = (~length, f) =>
  if length <= 0 {
    []
  } else {
    let arr = makeUninitializedUnsafe(length)
    for i in 0 to length - 1 {
      arr->setUnsafe(i, f(i))
    }
    arr
  }

@pure @val external isArray: 'a => bool = "Array.isArray"

@pure
external length: array<'a> => int = "%array_length"

let isEmpty = arr => arr->length === 0

let rec equalFromIndex = (a, b, i, eq, len) =>
  if i === len {
    true
  } else if eq(a->getUnsafe(i), b->getUnsafe(i)) {
    equalFromIndex(a, b, i + 1, eq, len)
  } else {
    false
  }

let equal = (a, b, eq) => {
  let len = a->length
  if len === b->length {
    equalFromIndex(a, b, 0, eq, len)
  } else {
    false
  }
}

let rec compareFromIndex = (a, b, i, cmp, len) =>
  if i === len {
    Stdlib_Ordering.equal
  } else {
    let c = cmp(a->getUnsafe(i), b->getUnsafe(i))
    if c == Stdlib_Ordering.equal {
      compareFromIndex(a, b, i + 1, cmp, len)
    } else {
      c
    }
  }

let compare = (a, b, cmp) => {
  let lenA = a->length
  let lenB = b->length
  lenA < lenB
    ? Stdlib_Ordering.less
    : lenA > lenB
    ? Stdlib_Ordering.greater
    : compareFromIndex(a, b, 0, cmp, lenA)
}

@send @mutates
external copyWithin: (array<'a>, ~target: int, ~start: int, ~end: int=?) => array<'a> = "copyWithin"

@mutates @send external pop: array<'a> => option<'a> = "pop"

@mutates @send external push: (array<'a>, 'a) => unit = "push"

@mutates @variadic @send external pushMany: (array<'a>, array<'a>) => unit = "push"

@mutates @send external reverse: array<'a> => unit = "reverse"
@pure @send external toReversed: array<'a> => array<'a> = "toReversed"

@mutates @send external shift: array<'a> => option<'a> = "shift"

@variadic @send @mutates
external splice: (array<'a>, ~start: int, ~remove: int, ~insert: array<'a>) => unit = "splice"

@variadic @send @pure
external toSpliced: (array<'a>, ~start: int, ~remove: int, ~insert: array<'a>) => array<'a> =
  "toSpliced"

@send @mutates
external removeInPlace: (array<'a>, int, @as(1) _) => unit = "splice"

@pure @send external with: (array<'a>, int, 'a) => array<'a> = "with"

@mutates @send external unshift: (array<'a>, 'a) => unit = "unshift"

@mutates @variadic @send external unshiftMany: (array<'a>, array<'a>) => unit = "unshift"

@pure @send external concat: (array<'a>, array<'a>) => array<'a> = "concat"
@pure @variadic @send external concatMany: (array<'a>, array<array<'a>>) => array<'a> = "concat"
let concatAll = arrays => concatMany([], arrays)

@pure @send external flat: array<array<'a>> => array<'a> = "flat"

@pure @send external includes: (array<'a>, 'a) => bool = "includes"

@pure @send external indexOf: (array<'a>, 'a, ~from: int=?) => int = "indexOf"

let indexOfOpt = (arr, item) =>
  switch arr->indexOf(item) {
  | -1 => None
  | index => Some(index)
  }

@pure @send external join: (array<string>, string) => string = "join"

@pure @send external joinUnsafe: (array<'a>, string) => string = "join"

@pure @send external lastIndexOf: (array<'a>, 'a, ~from: int=?) => int = "lastIndexOf"

let lastIndexOfOpt = (arr, item) =>
  switch arr->lastIndexOf(item) {
  | -1 => None
  | index => Some(index)
  }

@pure @send external slice: (array<'a>, ~start: int=?, ~end: int=?) => array<'a> = "slice"

@pure @send external copy: array<'a> => array<'a> = "slice"

@mutates @send external sort: (array<'a>, ('a, 'a) => Stdlib_Ordering.t) => unit = "sort"
@pure @send external toSorted: (array<'a>, ('a, 'a) => Stdlib_Ordering.t) => array<'a> = "toSorted"

@pure @send external toString: array<'a> => string = "toString"
@pure @send external toLocaleString: array<'a> => string = "toLocaleString"

@pure @send external every: (array<'a>, 'a => bool) => bool = "every"
@pure @send external everyWithIndex: (array<'a>, ('a, int) => bool) => bool = "every"

@pure @send external filter: (array<'a>, 'a => bool) => array<'a> = "filter"
@pure @send external filterWithIndex: (array<'a>, ('a, int) => bool) => array<'a> = "filter"

@pure @send external find: (array<'a>, 'a => bool) => option<'a> = "find"
@pure @send external findWithIndex: (array<'a>, ('a, int) => bool) => option<'a> = "find"

@pure @send external findLast: (t<'a>, 'a => bool) => option<'a> = "findLast"
@pure @send external findLastWithIndex: (t<'a>, ('a, int) => bool) => option<'a> = "findLast"

@pure @send external findIndex: (array<'a>, 'a => bool) => int = "findIndex"
@pure @send external findIndexWithIndex: (array<'a>, ('a, int) => bool) => int = "findIndex"

@pure @send external findLastIndex: (t<'a>, 'a => bool) => int = "findLastIndex"
@pure @send external findLastIndexWithIndex: (t<'a>, ('a, int) => bool) => int = "findLastIndex"

@pure @send external forEach: (array<'a>, 'a => unit) => unit = "forEach"
@pure @send external forEachWithIndex: (array<'a>, ('a, int) => unit) => unit = "forEach"

@pure @send external map: (array<'a>, 'a => 'b) => array<'b> = "map"
@pure @send external mapWithIndex: (array<'a>, ('a, int) => 'b) => array<'b> = "map"

@pure @send external reduce: (array<'b>, ('a, 'b) => 'a, 'a) => 'a = "reduce"
let reduce = (arr, init, f) => reduce(arr, f, init)
@pure @send external reduceWithIndex: (array<'b>, ('a, 'b, int) => 'a, 'a) => 'a = "reduce"
let reduceWithIndex = (arr, init, f) => reduceWithIndex(arr, f, init)

@send @pure
external reduceRight: (array<'b>, ('a, 'b) => 'a, 'a) => 'a = "reduceRight"

let reduceRight = (arr, init, f) => reduceRight(arr, f, init)

@send @pure
external reduceRightWithIndex: (array<'b>, ('a, 'b, int) => 'a, 'a) => 'a = "reduceRight"

let reduceRightWithIndex = (arr, init, f) => reduceRightWithIndex(arr, f, init)

@pure @send external some: (array<'a>, 'a => bool) => bool = "some"
@pure @send external someWithIndex: (array<'a>, ('a, int) => bool) => bool = "some"

@pure @get_index external get: (array<'a>, int) => option<'a> = ""
@mutates @set_index external set: (array<'a>, int, 'a) => unit = ""

@pure @get_index external getSymbol: (array<'a>, Stdlib_Symbol.t) => option<'b> = ""
@pure @get_index external getSymbolUnsafe: (array<'a>, Stdlib_Symbol.t) => 'b = ""
@mutates @set_index external setSymbol: (array<'a>, Stdlib_Symbol.t, 'b) => unit = ""

let findIndexOpt = (array: array<'a>, finder: 'a => bool): option<int> =>
  switch findIndex(array, finder) {
  | -1 => None
  | index => Some(index)
  }

let findLastIndexOpt = (array: array<'a>, finder: 'a => bool): option<int> =>
  switch findLastIndex(array, finder) {
  | -1 => None
  | index => Some(index)
  }

let swapUnsafe = (xs, i, j) => {
  let tmp = getUnsafe(xs, i)
  setUnsafe(xs, i, getUnsafe(xs, j))
  setUnsafe(xs, j, tmp)
}

module M = {
  @pure @val external floor: float => float = "Math.floor"
  @pure @val external random: unit => float = "Math.random"

  @pure
  external fromFloat: float => int = "%intoffloat"

  @pure
  external toFloat: int => float = "%identity"

  let random_int: (int, int) => int = (min, max) =>
    floor(random() *. toFloat(max - min))->fromFloat + min
}

let shuffle = xs => {
  let len = length(xs)
  for i in 0 to len - 1 {
    swapUnsafe(xs, i, M.random_int(i, len)) /* [i,len) */
  }
}

let toShuffled = xs => {
  let result = copy(xs)
  shuffle(result)
  result
}

let filterMap = (a, f) => {
  let l = length(a)
  let r = makeUninitializedUnsafe(l)
  let j = ref(0)
  for i in 0 to l - 1 {
    let v = getUnsafe(a, i)
    switch f(v) {
    | None => ()
    | Some(v) =>
      setUnsafe(r, j.contents, v)
      j.contents = j.contents + 1
    }
  }
  truncateToLengthUnsafe(r, j.contents)
  r
}

let keepSome = filterMap(_, x => x)

let filterMapWithIndex = (a, f) => {
  let l = length(a)
  let r = makeUninitializedUnsafe(l)
  let j = ref(0)
  for i in 0 to l - 1 {
    let v = getUnsafe(a, i)
    switch f(v, i) {
    | None => ()
    | Some(v) =>
      setUnsafe(r, j.contents, v)
      j.contents = j.contents + 1
    }
  }
  truncateToLengthUnsafe(r, j.contents)
  r
}

@pure @send external flatMap: (array<'a>, 'a => array<'b>) => array<'b> = "flatMap"
@pure @send external flatMapWithIndex: (array<'a>, ('a, int) => array<'b>) => array<'b> = "flatMap"

let findMap = (arr, f) => {
  let rec loop = i =>
    if i == arr->length {
      None
    } else {
      switch f(getUnsafe(arr, i)) {
      | None => loop(i + 1)
      | Some(_) as r => r
      }
    }

  loop(0)
}

let zip = (xs, ys) => {
  let (lenx, leny) = (length(xs), length(ys))
  let len = min(lenx, leny)
  let s = makeUninitializedUnsafe(len)
  for i in 0 to len - 1 {
    setUnsafe(s, i, (getUnsafe(xs, i), getUnsafe(ys, i)))
  }
  s
}

let zipBy = (xs, ys, f) => {
  let (lenx, leny) = (length(xs), length(ys))
  let len = min(lenx, leny)
  let s = makeUninitializedUnsafe(len)
  for i in 0 to len - 1 {
    setUnsafe(s, i, f(getUnsafe(xs, i), getUnsafe(ys, i)))
  }
  s
}

let partition = (a, f) => {
  let l = length(a)
  let i = ref(0)
  let j = ref(0)
  let a1 = makeUninitializedUnsafe(l)
  let a2 = makeUninitializedUnsafe(l)
  for ii in 0 to l - 1 {
    let v = getUnsafe(a, ii)
    if f(v) {
      setUnsafe(a1, i.contents, v)
      i.contents = i.contents + 1
    } else {
      setUnsafe(a2, j.contents, v)
      j.contents = j.contents + 1
    }
  }
  truncateToLengthUnsafe(a1, i.contents)
  truncateToLengthUnsafe(a2, j.contents)
  (a1, a2)
}

let unzip = a => {
  let l = length(a)
  let a1 = makeUninitializedUnsafe(l)
  let a2 = makeUninitializedUnsafe(l)
  for i in 0 to l - 1 {
    let (v1, v2) = getUnsafe(a, i)
    setUnsafe(a1, i, v1)
    setUnsafe(a2, i, v2)
  }
  (a1, a2)
}

@pure @send external at: (array<'a>, int) => option<'a> = "at"

let last = a => a->get(a->length - 1)

@pure
external ignore: array<'a> => unit = "%ignore"

@send @pure
external entries: array<'a> => Stdlib_IteratorObject.t<(int, 'a), unit, unknown> = "entries"

@send @pure
external values: array<'a> => Stdlib_IteratorObject.t<'a, unit, unknown> = "values"
