type user = {
  id: int,
  name: string,
  email: string,
  passwordHash: string,
  nickname?: string,
}

// What the API returns: a user without the email and the password hash.
type publicUser = {
  id: int,
  name: string,
  nickname?: string,
  avatar?: string,
}

let ada: user = {id: 1, name: "Ada", email: "ada@example.com", passwordHash: "x91f", nickname: "countess"}
let grace: user = {id: 2, name: "Grace", email: "grace@example.com", passwordHash: "b07c"}

let shown: publicUser = Convert.to(ada)
Console.log(shown)
Console.log([ada, grace]->Array.map((user): publicUser => Convert.to(user)))

// A field the source cannot give is a compile error at the call:
// type login = {name: string, password: string}
// let login: login = Convert.to(ada)
