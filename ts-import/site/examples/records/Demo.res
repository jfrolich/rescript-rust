let {getUser, rename} = %ts("./users.ts")

// `User` became the record type `user`: fields are checked, an optional
// field may be left out, and `string | null` is `Null.t<string>`.
let ada = rename(
  {
    id: "1",
    name: "ada",
    email: Null.null,
    tags: ["admin"],
    address: {street: "Mainstreet 1", city: "London"},
  },
  "Ada",
)

let city = ada.address.city

// `Promise<User | undefined>` is `promise<option<user>>`.
let greet = async id =>
  switch await getUser(id) {
  | Some({name, age: ?Some(age)}) => `${name}, ${Float.toString(age)}`
  | Some({name}) => name
  | None => "nobody"
  }
