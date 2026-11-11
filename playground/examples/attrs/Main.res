type user = {id: int, name: string}

type api = {
  load: int => user,
  save: (user, bool) => unit,
  count: unit => int,
}

// Every field is `@warning("-27") (arg1: ...) => throw(...)`.
let mock: api = Mock.make()

// A test replaces what it uses. The rest fails when it is reached.
let api = {...mock, count: () => 3}
Console.log(api.count())
Console.log(
  try api.load(1).name catch {
  | Failure(message) => message
  },
)

// The attribute on a whole record, with the number as an argument:
// `user` and `notify` are not used, and nothing is reported.
let silent: api = %Mock.allow(
  27,
  {
    load: id => {id, name: "nobody"},
    save: (user, notify) => (),
    count: () => 0,
  },
)
Console.log(silent.load(7))
