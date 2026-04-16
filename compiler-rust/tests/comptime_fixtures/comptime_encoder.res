// Full comptime encoder test
// Tests: @typeInfo, switch elimination, Record destructuring,
// inline for, field.name, @field, @compileError

type address = {street: string, city: string}
type user = {name: string, age: int, address: address}

let myUser: user = {
  name: "Alice",
  age: 30,
  address: {street: "Main St", city: "NYC"},
}

// Encode a string field
let encodedName = switch @typeInfo(string) {
| String => myUser.name
| _ => @compileError("expected string")
}

// Encode using @typeInfo on a record — pick the Record branch
let isRecord = switch @typeInfo(user) {
| Record(_) => true
| _ => false
}

// Destructure Record to get the type name
let typeName = switch @typeInfo(user) {
| Record({name}) => name
| _ => "unknown"
}

// Access each field name via inline for
let fieldCheck = switch @typeInfo(user) {
| Record({fields}) => {
    inline for field in fields {
      let _name = field.name
    }
    "fields accessed"
  }
| _ => "not a record"
}

// Use @field to access record fields by comptime-known name
let nameValue = {
  let v = @field(myUser, "name")
  v
}

let ageValue = {
  let v = @field(myUser, "age")
  v
}
