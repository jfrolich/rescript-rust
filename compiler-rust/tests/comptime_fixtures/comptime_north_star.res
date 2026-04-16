// ═══════════════════════════════════════════════════════════════════
// North-star comptime encoder test
//
// Demonstrates the full comptime encoder pattern:
// - Polymorphic @comptime function
// - @typeInfo(value) resolves per call site
// - switch @typeInfo branches eliminated at compile time
// - Record({fields}) destructuring
// - inline for over fields
// - @field(value, field.name) typed field access
// - Recursive @comptime calls for nested types
// - @compileError for unsupported types
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

// ── Generic comptime type describer (simulates encoder dispatch) ──

@comptime
let rec describeType = (value) => {
  switch @typeInfo(value) {
  | String => "string"
  | Int => "int"
  | Bool => "bool"
  | Float => "float"
  | Record({name}) => "record:" ++ name
  | _ => @compileError("unsupported type")
  }
}

let myUser: user = {
  name: "Alice",
  age: 30,
  active: true,
  address: {street: "123 Main St", city: "NYC", zip: 10001},
}

// ── Test: describeType specializes per type ──

let t1 = describeType(myUser)           // "record:user"
let t2 = describeType(myUser.name)      // "string"
let t3 = describeType(myUser.age)       // "int"
let t4 = describeType(myUser.active)    // "bool"
let t5 = describeType(myUser.address)   // "record:address"

// ── Test: inline for + @field + recursive describeType ──

let fieldTypes = switch @typeInfo(user) {
| Record({fields}) => {
    inline for field in fields {
      let _ = describeType(@field(myUser, field.name))
    }
    "all fields described"
  }
| _ => @compileError("expected record")
}

// ── Test: @comptime function doing full field walk ──

@comptime
let describeFields = (value) => {
  switch @typeInfo(value) {
  | Record({fields}) => {
      inline for field in fields {
        let _ = field.name
        let _ = describeType(@field(value, field.name))
      }
      "described"
    }
  | _ => "not a record"
  }
}

let described = describeFields(myUser)
let describedAddr = describeFields(myUser.address)
