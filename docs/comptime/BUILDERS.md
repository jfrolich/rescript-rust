# Comptime Builder Design

## TypeInfo Types (using optional fields)

```rescript
type rec typeInfo =
  | Int
  | Float
  | String
  | Bool
  | Unit
  | Record({
      name: string,
      fields: array<fieldInfo>,
      unboxed?: bool,
    })
  | Variant({
      name: string,
      constructors: array<constructorInfo>,
      unboxed?: bool,
    })
  | Array({element: typeInfo})
  | Option({inner: typeInfo})
  | Tuple({elements: array<typeInfo>})
  | Function({args: array<typeInfo>, returnType: typeInfo})
  | External({name: string})
  | Opaque({name: string})
  | Unknown

and fieldInfo = {
  name: string,
  typ: typeInfo,
  optional?: bool,
  mutable_?: bool,
}

and constructorInfo = {
  name: string,
  payload?: constructorPayload,
}

and constructorPayload =
  | Single(typeInfo)
  | Tuple(array<typeInfo>)
  | InlineRecord(array<fieldInfo>)
```

Optional fields use `?` so construction is clean:
```rescript
// Most fields are not optional/mutable, so defaults reduce noise:
{name: "age", typ: Int}
// vs without optionals:
{name: "age", typ: Int, optional: false, mutable_: false}
```

## Builders

### `@record(fields)` — Build a record from comptime field specifications

```rescript
// In a decoder:
let obj = JSON.Decode.object(json)
@record(
  inline for field in fields {
    {name: field.name, value: decode(Dict.getExn(obj, field.name))}
  }
)
```

The `@record` builtin takes an array of `{name: string, value: 'a}` where `name` is comptime-known. The compiler:
1. Validates all required record fields are present
2. Type-checks each value against the corresponding field type
3. Produces a `Texp_record` node in the typed tree

This generates:
```javascript
{
  name: JSON.Decode.string(obj["name"]),
  age: JSON.Decode.int(obj["age"]),
  // ...
}
```

### `@variant(name, payload?)` — Build a variant constructor

```rescript
@variant("Circle", {radius: decodedRadius})  // → Circle({radius: decodedRadius})
@variant("Point")                             // → Point
@variant("Some", decodedValue)                // → Some(decodedValue)
```

The compiler:
1. Validates the constructor name exists on the target type
2. Type-checks the payload against the constructor's expected arguments
3. Produces a `Texp_construct` node

### `@matchVariant(value, constructors)` — Pattern match a variant by comptime constructor list

```rescript
// In an encoder:
@matchVariant(value, constructors, (ctor, payload) => {
  let dict = Dict.make()
  Dict.set(dict, "tag", JSON.Encode.string(ctor.name))
  switch ctor.payload {
  | None => ()
  | Some(Single(_)) =>
    Dict.set(dict, "value", encode(payload))
  | Some(InlineRecord(fields)) =>
    inline for field in fields {
      Dict.set(dict, field.name, encode(@field(payload, field.name)))
    }
  | Some(Tuple(types)) =>
    inline for (i, typ) in types {
      Dict.set(dict, "_" ++ Int.toString(i), encode(@tupleField(payload, i)))
    }
  }
  JSON.Encode.object(dict)
})
```

This generates a switch expression with one arm per constructor:
```javascript
switch (value.TAG) {
  case "Circle":
    let dict = {};
    dict["tag"] = "Circle";
    dict["radius"] = JSON.Encode.float(value.radius);
    return JSON.Encode.object(dict);
  case "Point":
    let dict = {};
    dict["tag"] = "Point";
    return JSON.Encode.object(dict);
  // ...
}
```

## Realistic Encoder Example

```rescript
@comptime
let rec encode = (value) => {
  switch @typeInfo(value) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Float => JSON.Encode.float(value)
  | Bool => JSON.Encode.bool(value)
  | Option({inner}) =>
    switch value {
    | Some(v) => encode(v)
    | None => JSON.Encode.null
    }
  | Array({element}) =>
    JSON.Encode.array(value, item => encode(item))
  | Record({fields}) => {
      let dict = Dict.make()
      inline for field in fields {
        if field.optional {
          switch @field(value, field.name) {
          | Some(v) => Dict.set(dict, field.name, encode(v))
          | None => ()
          }
        } else {
          Dict.set(dict, field.name, encode(@field(value, field.name)))
        }
      }
      JSON.Encode.object(dict)
    }
  | Variant({constructors}) =>
    @matchVariant(value, constructors, (ctor, payload) => {
      let dict = Dict.make()
      Dict.set(dict, "tag", JSON.Encode.string(ctor.name))
      switch ctor.payload {
      | None => ()
      | Some(Single(_)) => Dict.set(dict, "value", encode(payload))
      | Some(InlineRecord(fields)) =>
        inline for field in fields {
          Dict.set(dict, field.name, encode(@field(payload, field.name)))
        }
      }
      JSON.Encode.object(dict)
    })
  | _ => @compileError("Cannot encode this type")
  }
}
```

## Realistic Decoder Example

```rescript
@comptime
let rec decode = (json) => {
  switch @typeInfo(json) {
  | String => JSON.Decode.string(json)
  | Int => JSON.Decode.int(json)
  | Float => JSON.Decode.float(json)
  | Bool => JSON.Decode.bool(json)
  | Option({inner}) =>
    switch JSON.Decode.nullable(json) {
    | Some(v) => Some(decode(v))
    | None => None
    }
  | Array({element}) =>
    JSON.Decode.array(json, item => decode(item))
  | Record({fields}) => {
      let obj = JSON.Decode.object(json)
      @record(
        inline for field in fields {
          if field.optional {
            {name: field.name, value: switch Dict.get(obj, field.name) {
            | Some(v) => Some(decode(v))
            | None => None
            }}
          } else {
            {name: field.name, value: decode(Dict.getExn(obj, field.name))}
          }
        }
      )
    }
  | Variant({constructors}) => {
      let obj = JSON.Decode.object(json)
      let tag = JSON.Decode.string(Dict.getExn(obj, "tag"))
      switch tag {
      inline for ctor in constructors {
      | ctor.name =>
        switch ctor.payload {
        | None => @variant(ctor.name)
        | Some(Single(_)) => @variant(ctor.name, decode(Dict.getExn(obj, "value")))
        | Some(InlineRecord(fields)) =>
          @variant(ctor.name, @record(
            inline for field in fields {
              {name: field.name, value: decode(Dict.getExn(obj, field.name))}
            }
          ))
        }
      }
      }
    }
  | _ => @compileError("Cannot decode this type")
  }
}
```

## What's Implemented vs TODO

### Implemented ✅
- `typeInfo` as predefined type with constructors
- `@typeInfo(typeName)` resolves to literal value
- `switch @typeInfo(T)` branch elimination in type checker
- `Record({name, fields})` destructuring with comptime bindings
- `inline for field in fields` unrolling
- `field.name` comptime field access
- `@field(value, comptimeName)` validated field access → Texp_field
- `@comptime` function inlining with parameter binding
- `@compileError("msg")` compile-time error
- Lambda switch constant folding for variants

### TODO for encoder
- `@typeInfo(value)` on expressions (infer type from static type)
- Recursive `@comptime` calls (`encode(@field(value, field.name))`)
- `field.optional` comptime boolean access (for conditional encoding)
- `@matchVariant` for variant encoding
- `Variant({constructors})` in typeInfo

### TODO for decoder
- `@record(fields)` record builder
- `@variant(name, payload?)` variant builder
- Recursive `@comptime` calls for nested decoding

### TODO for both
- `@comptime.inline` + Boa for user helper functions
- `constructorPayload` type for variant arg inspection
- Poly variant support in typeInfo
- Tuple support in typeInfo
