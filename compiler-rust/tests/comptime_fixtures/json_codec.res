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
// Returns result<T, string> so decoding failures are explicit.

@comptime
let rec decode = (json: JSON.t): result<_, string> => {
  switch @typeInfo(@return) {
  | String =>
    switch json {
    | String(s) => Ok(s)
    | _ => Error("expected string")
    }
  | Int =>
    switch json {
    | Number(n) => Ok(Float.toInt(n))
    | _ => Error("expected int")
    }
  | Float =>
    switch json {
    | Number(n) => Ok(n)
    | _ => Error("expected float")
    }
  | Bool =>
    switch json {
    | Boolean(b) => Ok(b)
    | _ => Error("expected bool")
    }
  | Record({fields}) =>
    switch json {
    | Object(dict) =>
      @record(inline for field in fields {
        switch decode(Dict.getUnsafe(dict, field.name)) {
        | Ok(v) => v
        | Error(e) => return Error(field.name ++ ": " ++ e)
        }
      })
      ->Ok
    | _ => Error("expected object")
    }
  | Option(_) =>
    switch json {
    | Null => Ok(None)
    | _ =>
      switch decode(json) {
      | Ok(v) => Ok(Some(v))
      | Error(e) => Error(e)
      }
    }
  | Array(_) =>
    json
    ->JSON.Decode.array
    ->Option.mapOr(Error("expected array"), arr => {
      let result = []
      for i in 0 to Array.length(arr) - 1 {
        switch decode(Array.getUnsafe(arr, i)) {
        | Ok(v) => result->Array.push(v)
        | Error(e) => return Error("[" ++ Int.toString(i) ++ "]: " ++ e)
        }
      }
      Ok(result)
    })
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

let decoded: result<user, string> = decode(json)

// ── Roundtrip primitives ─────────────────────────────────────────────

let s: result<string, string> = decode(encode("hello"))
let n: result<int, string> = decode(encode(42))
let b: result<bool, string> = decode(encode(true))

// ── Roundtrip nested ─────────────────────────────────────────────────

let addr: result<address, string> = decode(encode(alice.address))
