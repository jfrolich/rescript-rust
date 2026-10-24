# Comptime Implementation Notes

> These notes describe the prototype that was removed from the Rust compiler
> before release. They record what worked, as input for a future
> implementation; the code they refer to no longer exists.

## Core Design

The comptime system has three components:

1. **`@comptime` functions are inlined at call sites** — so the type checker sees concrete types
2. **`@typeInfo(expr)` is a builtin** — returns a `typeInfo` value based on the static type of `expr`. Requires a concrete type (no type variables).
3. **The existing compiler optimizer** handles switch folding, constant propagation, dead branch elimination

There is no special "comptime mode." The type checker handles `@typeInfo`, `@field`, and `inline for` as general capabilities. The `@comptime` attribute just means "inline this function."

## `@typeInfo` Requires Concrete Types

`@typeInfo(expr)` looks at `expr`'s static type. It must be fully resolved — no type variables:

```rescript
@typeInfo(myUser)        // ✅ myUser: user — concrete
@typeInfo(myString)      // ✅ myString: string — concrete
@typeInfo(items)         // ✅ items: array<string> — concrete
@typeInfo(x)             // ❌ x: 'a — Error: @typeInfo requires a concrete type
```

The `@comptime` inlining ensures types are concrete: the function body is inlined with the call site's concrete types.

## How It Works: Nested Encoder Example

```rescript
type address = { street: string, city: string }
type user = { name: string, age: int, address: address, tags: array<string>, email: option<string> }

@comptime
let rec encode = (value) => {
  switch @typeInfo(value) {
  | String => Json.string(value)
  | Int => JSON.Encode.int((value))
  | Record({fields}) =>
    let obj = Dict.empty()
    inline for field in fields {
      Dict.set(obj, field.name, encode(@field(value, field.name)))
    }
    Json.object_(obj)
  | Array({element}) =>
    value->Array.map(item => encode(item))->Json.array
  | Option({inner}) =>
    switch value {
    | Some(v) => encode(v)
    | None => Json.null
    }
  }
}

let json = encode(myUser)
```

### Step-by-step: `encode(myUser)` where myUser: user

**1. Inline.** `encode` is `@comptime`. The compiler inlines its body with `value = myUser` (type: `user`).

**2. `@typeInfo(value)`.** The type checker sees `value: user`. Calls `build_type_info(user)` → `Record({name: "user", fields: [name: String, age: Int, address: Record(address), tags: Array(String), email: Option(String)]})`. Returns a literal `typeInfo` value.

**3. Switch.** Scrutinee is known `Record({fields})`. Matches the `Record` branch. **Skips** String, Int, Array, Option branches (never type-checked — important because e.g. `Json.string(value)` where `value: user` would fail).

**4. `inline for field in fields`.** `fields` is known (5 elements). Type checker unrolls — type-checks the body 5 times:

**Iteration: "name" (String)**
- `field.name` → `"name"` (comptime constant)
- `@field(value, "name")` → validates "name" exists on user → `myUser.name: string`
- `encode(myUser.name)` → inline → `@typeInfo` → String → `Json.string(myUser.name)`
- Emit: `Dict.set(obj, "name", Json.string(myUser.name))`

**Iteration: "age" (Int)**
- `encode(myUser.age)` → Int → `JSON.Encode.int((myUser.age))`

**Iteration: "address" (Record)**
- `encode(myUser.address)` → Record(address) → nested `inline for` over street, city
- Produces: `let obj$1 = Dict.empty(); Dict.set(obj$1, "street", ...); Dict.set(obj$1, "city", ...); Json.object_(obj$1)`

**Iteration: "tags" (Array\<String\>)**
- `encode(myUser.tags)` → `Array({element: String})`
- Body: `value->Array.map(item => encode(item))->Json.array`
- `item: string` (concrete — from `array<string>`) → `encode(item)` inlines → `Json.string(item)`
- Result: `myUser.tags->Array.map(item => Json.string(item))->Json.array`

**Iteration: "email" (Option\<String\>)**
- `encode(myUser.email)` → `Option({inner: String})`
- Body: `switch value { | Some(v) => encode(v) | None => Json.null }`
- This is a **runtime switch** (value is runtime). Type checker checks both branches:
  - `Some(v)` → `v: string` → `encode(v)` → String → `Json.string(v)` ✅
  - `None` → `Json.null` ✅

### Final JS output

```javascript
let obj = Dict.empty();
Dict.set(obj, "name", Json.string(myUser.name));
Dict.set(obj, "age", JSON.Encode.int((myUser.age)));
let obj$1 = Dict.empty();
Dict.set(obj$1, "street", Json.string(myUser.address.street));
Dict.set(obj$1, "city", Json.string(myUser.address.city));
Dict.set(obj, "address", Json.object_(obj$1));
Dict.set(obj, "tags", myUser.tags->Array.map(item => Json.string(item))->Json.array);
Dict.set(obj, "email", myUser.email !== undefined ? Json.string(myUser.email) : Json.null);
let json = Json.object_(obj);
```

## What `type_expect` Does

These are general type checker capabilities, not comptime-specific:

| Expression | What happens |
|---|---|
| `@typeInfo(expr)` | Look up expr's static type (must be concrete). Build TypeInfo. Return literal `typeInfo` value. |
| `switch <known variant> { cases }` | Match known value against patterns. Type-check ONLY matching branch. Skip others. |
| `inline for x in <known array> { body }` | Unroll: type-check body N times with x bound to each element. Splice results as sequence. |
| `@field(value, <known string>)` | Validate field exists on value's type. Produce `Texp_field` with correct type. Compile error if field doesn't exist. |
| `f(arg)` where f is `@comptime` | Inline f's body. Type-check with arg's concrete type. |

## Two Comptime Mechanisms

### `@comptime` — Specialization via Inlining

Function body inlined at each call site. Type checker type-checks with concrete types. `@typeInfo`, `@field`, `inline for` are builtins. Optimizer folds switches.

No JS engine needed.

### `@comptime.inline` — Full Evaluation in JS Engine (Boa)

Entire function executes at compile time. All arguments must be comptime-known (literals, typeInfo values, results of other comptime.inline calls). Compiled to JS, executed in Boa, result inlined as constant.

```rescript
@comptime.inline
let capitalize = (s: string): string => {
  String.charAt(s, 0)->String.toUpperCase ++ String.sliceToEnd(s, ~start=1)
}
```

Called with comptime-known argument → Boa evaluates → result inlined.
Called with runtime argument → compile error.

### Composition

```rescript
@comptime.inline
let capitalize = (s: string): string => { ... }

@comptime
let rec encode = (value) => {
  switch @typeInfo(value) {
  | Record({fields}) =>
    inline for field in fields {
      Dict.set(obj, capitalize(field.name), encode(@field(value, field.name)))
      //            ^^^^^^^^^^^^^^^^^^^^^^
      //            field.name is "name" (comptime-known from inline for)
      //            capitalize("name") → Boa evaluates → "Name"
    }
  }
}
```

## Lambda Switch Constant Folding ✅ DONE

`Lswitch` on known constant → pick matching branch directly.
`switch Red { | Red => "red" | Green => "green" }` → `"red"`.

## Implementation Order

1. ✅ **Lambda switch constant folding**
2. **`typeInfo` as predefined type** — variant type with Record, String, Int, etc. constructors
3. **`@typeInfo(expr)` in type checker** — resolve static type, construct literal typeInfo value
4. **Skip non-matching switch branches** — type-check only the branch that matches the known scrutinee
5. **`inline for` unrolling** — type-check body N times with bound variable
6. **`@field(value, name)` validation + generation** — validate field, produce Texp_field
7. **`@comptime` inlining** — inline function body at call sites
8. **`@comptime.inline` + Boa** — full compile-time evaluation
