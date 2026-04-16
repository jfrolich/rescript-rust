// Comptime JSON Codec
//
// Generic encoder and decoder using @comptime + @typeInfo.
// Both functions specialize at compile time — no runtime type dispatch.

type address = {
  street: string,
  city: string,
}

type user = {
  name: string,
  age: int,
  active: bool,
  address: address,
}

// ── Encoder ──────────────────────────────────────────────────────────
//
// Specializes per call-site type. Since JSON.Encode.* are all %identity,
// the output is just Dict operations and raw values — zero overhead.

@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Float => JSON.Encode.float(value)
  | Bool => JSON.Encode.bool(value)
  | Record({fields}) =>
    let dict = Dict.make()
    inline for field in fields {
      Dict.set(dict, field.name, encode(@field(value, field.name)))
    }
    JSON.Encode.object(dict)
  | Option(_) =>
    switch value {
    | Some(v) => encode(v)
    | None => JSON.Encode.null
    }
  | Array(_) =>
    JSON.Encode.array(Array.map(value, v => encode(v)))
  | _ => @compileError("encode: unsupported type")
  }
}

// ── Decoder ──────────────────────────────────────────────────────────
//
// Also specializes per call-site. Uses the expected return type to
// determine which JSON branch to take and how to build records.

@comptime
let rec decode = (json: JSON.t) => {
  switch @typeInfo(@return) {
  | String =>
    switch json {
    | String(s) => s
    | _ => panic("expected string")
    }
  | Int =>
    switch json {
    | Number(n) => Float.toInt(n)
    | _ => panic("expected int")
    }
  | Float =>
    switch json {
    | Number(n) => n
    | _ => panic("expected float")
    }
  | Bool =>
    switch json {
    | Boolean(b) => b
    | _ => panic("expected bool")
    }
  | Record({fields}) =>
    switch json {
    | Object(dict) =>
      @record(inline for field in fields {
        decode(Dict.getUnsafe(dict, field.name))
      })
    | _ => panic("expected object")
    }
  | Option(_) =>
    switch json {
    | Null => None
    | _ => Some(decode(json))
    }
  | Array(_) =>
    switch json {
    | Array(arr) => Array.map(arr, item => decode(item))
    | _ => panic("expected array")
    }
  | _ => @compileError("decode: unsupported type")
  }
}

// ── Test data ────────────────────────────────────────────────────────

let alice: user = {
  name: "Alice",
  age: 30,
  active: true,
  address: {street: "Main St", city: "NYC"},
}

// ── Encode ───────────────────────────────────────────────────────────

let json = encode(alice)

// ── Decode ───────────────────────────────────────────────────────────

let decoded: user = decode(json)

// ── Roundtrip primitives ─────────────────────────────────────────────

let s: string = decode(encode("hello"))
let n: int = decode(encode(42))
let b: bool = decode(encode(true))

// ── Roundtrip nested ─────────────────────────────────────────────────

let addr: address = decode(encode(alice.address))
