// ═══════════════════════════════════════════════════════════════════
// Full comptime encoder test
//
// Uses only primitives — no stdlib needed.
// Simulates encoding by building string representations.
// ═══════════════════════════════════════════════════════════════════

type address = {
  street: string,
  city: string,
}

type user = {
  name: string,
  age: int,
  address: address,
}

// ── Recursive comptime type encoder ──

@comptime
let rec encodeValue = (value) => {
  switch @typeInfo(value) {
  | String => "\"" ++ value ++ "\""
  | Int => "int"
  | Bool => "bool"
  | Float => "float"
  | Record({name, fields}) => {
      let result = ref("{")
      inline for field in fields {
        let encoded = encodeValue(@field(value, field.name))
        result := result.contents ++ "\"" ++ field.name ++ "\":" ++ encoded ++ ","
      }
      result.contents ++ "}"
    }
  | _ => @compileError("unsupported type")
  }
}

let myUser: user = {
  name: "Alice",
  age: 30,
  address: {street: "Main St", city: "NYC"},
}

// ── Test: encode primitives ──
let enc_string = encodeValue("hello")
let enc_name = encodeValue(myUser.name)

// ── Test: encode full record (recursive) ──
let enc_user = encodeValue(myUser)
