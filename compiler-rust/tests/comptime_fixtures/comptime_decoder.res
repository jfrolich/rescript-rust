// ═══════════════════════════════════════════════════════════════════
// Comptime decoder test
//
// Tests @record builder for constructing typed records
// from decoded field values.
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

// ── Simple decoder: build records from decoded values ──

// Simulate decoding a flat record
let decodedAddress: address = @record(address, "street", "123 Main", "city", "NYC")

// Simulate decoding a nested record
let decodedUser: user = @record(user,
  "name", "Alice",
  "age", 30,
  "address", @record(address, "street", "Main St", "city", "Springfield")
)

// ── @comptime decoder function ──

@comptime
let decodeAddress = (street: string, city: string) => {
  @record(address, "street", street, "city", city)
}

let addr = decodeAddress("Oak Ave", "Boston")

// ── Type-safe: wrong field name is compile error ──
// let bad: user = @record(user, "name", "Bob", "age", 25, "wrong", "x")
// Would produce: @record: field 'wrong' not found on type 'user'
