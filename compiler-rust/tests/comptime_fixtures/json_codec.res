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
// Specializes per call-site type. @typeInfo(value) resolves from the
// argument's type, so no explicit type parameter needed.
//
// Since JSON.Encode.* are all %identity, the output is just Dict
// operations and raw values — zero overhead.

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
// Unlike the encoder, the decoder has no value to infer the target type
// from — it receives opaque JSON. So it takes an explicit comptime type
// parameter: decode(user, json) tells it to produce a user.
//
// @typeInfo(t) resolves the comptime type parameter, and each recursive
// call passes the field's type: decode(field.type, ...).

@comptime
let rec decode = (type t, json: JSON.t): result<t, string> => {
  switch @typeInfo(t) {
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
      @record(t, inline for field in fields {
        switch decode(field.type, Dict.getUnsafe(dict, field.name)) {
        | Ok(v) => v
        | Error(e) => return Error(field.name ++ ": " ++ e)
        }
      })
      ->Ok
    | _ => Error("expected object")
    }
  | Option({inner}) =>
    switch json {
    | Null => Ok(None)
    | _ =>
      switch decode(inner, json) {
      | Ok(v) => Ok(Some(v))
      | Error(e) => Error(e)
      }
    }
  | Array({element}) =>
    json
    ->JSON.Decode.array
    ->Option.mapOr(Error("expected array"), arr => {
      let result = []
      for i in 0 to Array.length(arr) - 1 {
        switch decode(element, Array.getUnsafe(arr, i)) {
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

let decoded = decode(user, json)

// ── Roundtrip primitives ─────────────────────────────────────────────

let s = decode(string, encode("hello"))
let n = decode(int, encode(42))
let b = decode(bool, encode(true))

// ── Roundtrip nested ─────────────────────────────────────────────────

let addr = decode(address, encode(alice.address))
