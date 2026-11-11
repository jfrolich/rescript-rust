type user = {name: string, age: int, email: string}

type userPatch = %Partial.t(user)

let apply = (user: user, patch: userPatch): user => {
  name: patch.name->Option.getOr(user.name),
  age: patch.age->Option.getOr(user.age),
  email: patch.email->Option.getOr(user.email),
}

let alice: user = {name: "Alice", age: 30, email: "alice@example.com"}

Console.log(alice->apply({age: 31}))
