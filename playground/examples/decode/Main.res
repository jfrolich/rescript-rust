type address = {street: string, city: string}

type user = {
  name: string,
  age: int,
  email: option<string>,
  addresses: array<address>,
}

let json = JSON.parseOrThrow(`{
  "name": "Alice",
  "age": 30,
  "email": null,
  "addresses": [{"street": "Main St 1", "city": "Utrecht"}]
}`)

// The annotation is what the macro decodes to.
let user: user = Decode.fromJson(json)

Console.log(user)
Console.log(user.addresses->Array.map(address => address.city))

// Something that is not a user fails at run time, with a message:
let broken = try {
  let user: user = Decode.fromJson(JSON.parseOrThrow(`{"name": 1}`))
  user.name
} catch {
| Decode.DecodeError(message) => "Not a user: " ++ message
}
Console.log(broken)
