// Full comptime encoder test
// Tests all working comptime features end-to-end

type address = {
  street: string,
  city: string,
  zip: int,
}

type user = {
  name: string,
  age: int,
  address: address,
  active: bool,
}

let myUser: user = {
  name: "Alice",
  age: 30,
  address: {street: "123 Main St", city: "NYC", zip: 10001},
  active: true,
}

// ── Test 1: @typeInfo resolves record type ──
let isRecord = switch @typeInfo(user) {
| Record(_) => true
| _ => false
}

// ── Test 2: @typeInfo resolves primitives ──
let isString = switch @typeInfo(string) {
| String => true
| _ => false
}

let isInt = switch @typeInfo(int) {
| Int => true
| _ => false
}

let isBool = switch @typeInfo(bool) {
| Bool => true
| _ => false
}

let isFloat = switch @typeInfo(float) {
| Float => true
| _ => false
}

// ── Test 3: Record destructuring gets type name ──
let recordName = switch @typeInfo(user) {
| Record({name}) => name
| _ => "unknown"
}

// ── Test 4: Record destructuring gets fields ──
let fieldCount = switch @typeInfo(user) {
| Record({fields}) => {
    let count = ref(0)
    inline for _field in fields {
      count := count.contents + 1
    }
    count.contents
  }
| _ => 0
}

// ── Test 5: field.name resolves in inline for ──
let firstFieldName = switch @typeInfo(user) {
| Record({fields}) => {
    let result = ref("")
    inline for field in fields {
      if result.contents == "" {
        result := field.name
      }
    }
    result.contents
  }
| _ => ""
}

// ── Test 6: @field accesses record fields ──
let userName = {
  let v = @field(myUser, "name")
  v
}

let userAge = {
  let v = @field(myUser, "age")
  v
}

// ── Test 7: @field with comptime field name from inline for ──
let fieldValues = switch @typeInfo(user) {
| Record({fields}) => {
    inline for field in fields {
      let _ = @field(myUser, field.name)
    }
    "accessed all fields"
  }
| _ => "not a record"
}

// ── Test 8: @compileError on unsupported types ──
let safePrimitive = switch @typeInfo(int) {
| Int => "int is supported"
| String => "string is supported"
| _ => @compileError("unsupported type")
}

// ── Test 9: Nested record @typeInfo ──
let addressIsRecord = switch @typeInfo(address) {
| Record({name}) => name
| _ => "not a record"
}

// ── Test 10: @comptime function with full pattern ──
@comptime
let describeType = (value: user) => {
  switch @typeInfo(user) {
  | Record({name, fields}) => {
      let count = ref(0)
      inline for _field in fields {
        count := count.contents + 1
      }
      name
    }
  | _ => "not a record"
  }
}

let description = describeType(myUser)

// ── Test 11: @comptime with @field access ──
@comptime
let getFirstField = (value: user) => {
  let v = @field(value, "name")
  v
}

let firstName = getFirstField(myUser)

// ── Test 12: @comptime with inline for and @field ──
@comptime
let touchAllFields = (value: user) => {
  switch @typeInfo(user) {
  | Record({fields}) => {
      inline for field in fields {
        let _ = @field(value, field.name)
      }
      "done"
    }
  | _ => "fail"
  }
}

let touched = touchAllFields(myUser)
