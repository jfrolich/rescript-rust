// ═══════════════════════════════════════════════════════════════════
// Complete comptime encoder/decoder test
//
// Tests the full pattern: @comptime + @typeInfo + switch + inline for
// + @field + @record + recursive specialization + option/array
// ═══════════════════════════════════════════════════════════════════

type address = {
  street: string,
  city: string,
}

type user = {
  name: string,
  age: int,
  active: bool,
  email: option<string>,
  address: address,
}

// ═══ ENCODER ═══

@comptime
let rec encode = (value) => {
  switch @typeInfo(value) {
  | String => "s:" ++ value
  | Int => "i"
  | Bool => "b"
  | Float => "f"
  | Option(_) =>
    switch value {
    | Some(v) => encode(v)
    | None => "null"
    }
  | Array(_) => "array"
  | Record({name, fields}) => {
      let r = ref("{" ++ name ++ ":")
      inline for field in fields {
        let encoded = encode(@field(value, field.name))
        r := r.contents ++ field.name ++ "=" ++ encoded ++ ";"
      }
      r.contents ++ "}"
    }
  | _ => @compileError("encode: unsupported type")
  }
}

// ═══ DECODER (using @record) ═══

let decodeAddress = (street: string, city: string): address => {
  {street, city}
}

let decodeUser = (name: string, age: int, active: bool, email: option<string>, address: address): user => {
  {name, age, active, email, address}
}

// ═══ TEST DATA ═══

let myUser: user = {
  name: "Alice",
  age: 30,
  active: true,
  email: Some("alice@example.com"),
  address: {street: "123 Main St", city: "NYC"},
}

// ═══ ENCODER TESTS ═══

// Primitive encoding
let encString = encode("hello")
let encName = encode(myUser.name)

// Full record encoding (recursive, with option handling)
let encUser = encode(myUser)

// Nested record encoding
let encAddr = encode(myUser.address)

// ═══ DECODER TESTS ═══

// Decode an address
let decAddr = decodeAddress("Oak Ave", "Boston")

// Decode a full user with nested record
let decUser = decodeUser(
  "Bob",
  25,
  false,
  None,
  decodeAddress("Elm St", "LA"),
)
