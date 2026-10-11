%%raw(`
function jsOutputParityAdd(left, right) {
  return left + right
}
`)

type rec kind<_> =
  | Int: kind<int>
  | Text: kind<string>

@val external add: (int, int) => int = "jsOutputParityAdd"
@obj external config: (~kind: @ignore kind<'a>, ~high: int, ~low: 'a, unit) => _ = ""
@send external slice: (string, int, int) => string = "slice"
@get external length: string => int = "length"
@get_index external arrayGet: (array<string>, int) => option<string> = ""
@set_index external arraySet: (array<string>, int, string) => unit = ""

type target
@set external setValue: (target, @ignore kind<'a>, 'a) => unit = "value"
@get external getValue: (target, @ignore kind<'a>) => 'a = "value"

let numberConfig = config(~kind=Int, ~high=10, ~low=1, ())
let textConfig = config(~kind=Text, ~high=10, ~low="one", ())

let stringOps = value => {
  let size = length(value)
  (slice(value, 0, 1), size)
}

let arrayOps = values => {
  arraySet(values, 0, "first")
  switch arrayGet(values, 0) {
  | Some(value) => value
  | None => "missing"
  }
}

let ignoredSideEffect = () => {
  let counter = ref(0)
  let _obj = config(
    ~kind={
      counter := counter.contents + 1
      Int
    },
    ~high=add(1, 2),
    ~low=3,
    (),
  )
  counter.contents
}

let targetOps = target => {
  setValue(target, Text, "stored")
  getValue(target, Text)
}
