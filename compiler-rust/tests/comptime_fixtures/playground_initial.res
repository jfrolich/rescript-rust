// ── Comptime playground ─────────────────────────────────────────────────
// Functions marked @comptime run at compile time. @typeInfo introspects a
// type; Array.map / Array.forEach over comptime arrays unroll into specialized
// code. Each call monomorphizes to a specialized function — recursive types
// produce self-recursive code, no infinite expansion.

type address = { street: string, city: string }
type status = Active | Inactive | Pending
type user = { name: string, age: int, active: bool, status: status, address: address }
type tree = { value: string, children: array<tree> }

// Variant primitives:
//   @hasTag(v, "Name")      — runtime check: is `v` constructor "Name"?
//   @argAt(v, i, argType)   — runtime `v._<i>` typed as argType (comptime).
// Together with `constructors->Array.forEach(c => c.args->Array.forEach(...))`,
// they let the encoder recursively call `encode` on each argument with its
// real type — so `encode$float`, `encode$address`, etc. are emitted, not a
// uniform array<JSON.t>.

// ── 1. Zero-overhead JSON encoder ───────────────────────────────────────
// encode(alice) produces a specialized encode$user function. Since the
// JSON.Encode.* helpers are %identity, the output reduces to plain Dict
// assignments — no runtime type dispatch.

@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Bool => JSON.Encode.bool(value)
  | Record({fields}) =>
    let dict = Dict.make()
    fields->Array.forEach(field => {
      Dict.set(dict, field.name, encode(@field(value, field.name)))
    })
    JSON.Encode.object(dict)
  | Variant({constructors}) =>
    let result = ref(JSON.Null)
    constructors->Array.forEach(c => {
      if @hasTag(value, c.name) {
        let arr = [JSON.Encode.string(c.name)]
        c.args->Array.forEachWithIndex((argType, i) => {
          Array.push(arr, encode(@argAt(value, i, argType)))
        })
        result := JSON.Encode.array(arr)
      }
    })
    result.contents
  | Array(_) => JSON.Encode.array(Array.map(value, v => encode(v)))
  | _ => @compileError("encode: unsupported type")
  }
}

let alice: user = {
  name: "Alice",
  age: 30,
  active: true,
  status: Active,
  address: {street: "Main St", city: "NYC"},
}

let aliceJson = encode(alice)

// Recursive types: encode$tree calls itself via Array.map.
let myTree: tree = {
  value: "root",
  children: [
    {value: "child1", children: []},
    {value: "child2", children: []},
  ],
}
let treeJson = encode(myTree)

// ── 2. Decoder returning result<t, string> ──────────────────────────────
// The decoder has no value to infer from, so it takes a comptime type
// parameter: decode(user, json) specializes to decode$user. It returns
// `result<t, string>` — no throws. For records, each field is decoded and
// the first Error short-circuits through a mutable `err` ref.

@comptime
let rec decode = (type t, json: JSON.t): result<t, string> => {
  switch @typeInfo(t) {
  | String =>
    switch json { | String(s) => Ok(s) | _ => Error("expected string") }
  | Int =>
    switch json { | Number(n) => Ok(Float.toInt(n)) | _ => Error("expected int") }
  | Bool =>
    switch json { | Boolean(b) => Ok(b) | _ => Error("expected bool") }
  | Record({fields}) =>
    switch json {
    | Object(dict) => {
        let err = ref(None)
        let values = fields->Array.map(field =>
          switch decode(field.typ, Dict.getUnsafe(dict, field.name)) {
          | Ok(v) => v
          | Error(e) => {
              if err.contents == None { err := Some(e) }
              %raw(`null`)
            }
          }
        )
        switch err.contents {
        | None => Ok(@record(t, values))
        | Some(e) => Error(e)
        }
      }
    | _ => Error("expected object")
    }
  | Variant({constructors}) =>
    switch json {
    | Array(items) =>
      switch items[0] {
      | Some(String(name)) => {
          let result = ref(Error("unknown variant: " ++ name))
          constructors->Array.forEach(c => {
            if name == c.name { result := Ok(@constructor(t, c.name)) }
          })
          result.contents
        }
      | _ => Error("expected [name, ...] array")
      }
    | _ => Error("expected variant array")
    }
  | _ => @compileError("decode: unsupported type")
  }
}

let decodedAlice = decode(user, aliceJson)

// ── 3. Type-level comptime: keys of a record as a variant ───────────────
// @buildVariant consumes a list of @variantCase specs to emit a real
// variant type at compile time.

@comptime
let userKey =
  switch @typeInfo(user) {
  | Record({fields}) =>
    @buildVariant(fields->Array.map(field =>
      @variantCase({name: field.name})
    ))
  | _ => @compileError("expected record")
  }

let k1: userKey = Name
let k2: userKey = Age

// ── 4. Type-level comptime: make all fields of a record optional ────────
// `partial` takes a type and returns a new record type where every field
// is optional. `{...field, optional: true}` spreads the source field spec
// and overrides just the `optional` attribute.

@comptime
let partial = (type t) =>
  switch @typeInfo(t) {
  | Record({fields}) =>
    @buildRecord(fields->Array.map(field =>
      @recordField({...field, optional: true})
    ))
  | _ => @compileError("partial: expected record")
  }

@comptime
let partialUser = partial(user)

let patch: partialUser = { name: "Alice" }
