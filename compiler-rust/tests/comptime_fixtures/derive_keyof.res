@keyOf
type user = {
  name: string,
  age: int,
  email: string,
}

// Use the generated user_key type
let k: user_key = Name
let s = switch k {
| Name => "name"
| Age => "age"
| Email => "email"
}
