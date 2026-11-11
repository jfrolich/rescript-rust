type shape =
  | Circle({radius: float})
  | Rect({width: float, height: float})
  | Point

type user = {
  name: string,
  @Json.key("user_age") age: int,
  email: option<string>,
  tags: array<string>,
  avatar: shape,
}

let alice = {
  name: "Alice",
  age: 30,
  email: None,
  tags: ["admin", "staff"],
  avatar: Circle({radius: 2.5}),
}

Console.log(JSON.stringify(Json.encode(alice), ~space=2))

// The type can come from inference: nothing in the callback says `user`.
let team = [alice, {...alice, name: "Bob", avatar: Point}]
Console.log(team->Array.map(member => JSON.stringify(Json.encode(member.avatar))))

// A type the macro rejects is a compile error at the call:
// let bad = Json.encode((x: int) => x + 1)
