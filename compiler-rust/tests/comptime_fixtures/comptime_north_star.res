// ═══════════════════════════════════════════════════════════════════
// North-star comptime encoder test
//
// This is the target: a generic @comptime encoder that handles
// string, int, float, bool, option, array, and nested records.
// It should compile to specialized JS with NO runtime type dispatch.
// ═══════════════════════════════════════════════════════════════════

type address = {
  street: string,
  city: string,
  zip: int,
}

type user = {
  name: string,
  age: int,
  active: bool,
  address: address,
}

// ── The generic comptime encoder ──

@comptime
let rec encodeString = (value: string) => {
  switch @typeInfo(string) {
  | String => value  // just return the string for now (no JSON.Encode without stdlib)
  | _ => @compileError("expected string")
  }
}

@comptime
let rec encodeInt = (value: int) => {
  switch @typeInfo(int) {
  | Int => value
  | _ => @compileError("expected int")
  }
}

@comptime
let rec encodeBool = (value: bool) => {
  switch @typeInfo(bool) {
  | Bool => value
  | _ => @compileError("expected bool")
  }
}

// ── Encode user fields individually ──

let myUser: user = {
  name: "Alice",
  age: 30,
  active: true,
  address: {street: "123 Main St", city: "NYC", zip: 10001},
}

// These use @comptime functions that get inlined and specialized
let encodedName = encodeString(myUser.name)
let encodedAge = encodeInt(myUser.age)
let encodedActive = encodeBool(myUser.active)

// ── Encode using @typeInfo switch + inline for + @field ──

let fieldNames = switch @typeInfo(user) {
| Record({fields}) => {
    inline for field in fields {
      let _ = field.name
    }
    "done"
  }
| _ => @compileError("expected record")
}

let fieldAccess = switch @typeInfo(user) {
| Record({fields}) => {
    inline for field in fields {
      let _ = @field(myUser, field.name)
    }
    "accessed"
  }
| _ => @compileError("expected record")
}

// ── @comptime function that does the full pattern ──

@comptime
let encodeUser = (value: user) => {
  switch @typeInfo(user) {
  | Record({fields}) => {
      inline for field in fields {
        let _ = @field(value, field.name)
      }
      "encoded"
    }
  | _ => @compileError("encodeUser requires a record")
  }
}

let result = encodeUser(myUser)
