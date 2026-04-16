// Comptime decoder test using @record with inline for

type address = {
  street: string,
  city: string,
}

type user = {
  name: string,
  age: int,
  address: address,
}

// Decode address from a source record
let source_addr: address = {street: "123 Main", city: "NYC"}
let decoded_addr: address = switch @typeInfo(address) {
| Record({fields}) =>
  @record(address, inline for field in fields {
    @field(source_addr, field.name)
  })
| _ => @compileError("not a record")
}

// Decode user from a source record (with nested address)
let source_user: user = {name: "Alice", age: 30, address: {street: "Main St", city: "Springfield"}}
let decoded_user: user = switch @typeInfo(user) {
| Record({fields}) =>
  @record(user, inline for field in fields {
    @field(source_user, field.name)
  })
| _ => @compileError("not a record")
}
