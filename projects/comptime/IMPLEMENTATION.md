# Comptime Implementation Notes

## Core Insight: Inlining + Builtins + Existing Optimization

The comptime system is simpler than it first appears. There is no special "comptime mode" or separate partial evaluator. It's three things:

1. **`@comptime` functions are inlined at call sites** — so the type checker sees concrete types
2. **`@typeInfo(value)` is a builtin** that returns a `typeInfo` value based on the static type — works anywhere, not just in comptime
3. **The existing compiler optimizer** handles switch folding, constant propagation, and dead branch elimination

That's it. No comptime/runtime tracking, no special evaluation passes. The type checker just type-checks the inlined body with concrete types, and the optimizer cleans up.

## How It Works: Nested Encoder Example

```rescript
type address = { street: string, city: string }
type user = { name: string, age: int, address: address }

@comptime
let rec encode = (value) => {
  switch @typeInfo(value) {
  | String => Json.string(value)
  | Int => Json.number(Int.toFloat(value))
  | Record({fields}) =>
    let obj = Dict.empty()
    inline for field in fields {
      Dict.set(obj, field.name, encode(@field(value, field.name)))
    }
    Json.object_(obj)
  }
}

let json = encode(myUser)
```

### Step-by-step compilation of `encode(myUser)`

**1. Inline the body.** `encode` is `@comptime`, so the compiler inlines its body at the call site with `value = myUser` (type: `user`).

**2. Type-check `@typeInfo(value)`.** The type checker sees `Pexp_comptime_typeinfo`. It looks at `value`'s type → `user`. It calls `build_type_info(user)` → returns `Record({name: "user", fields: [...]})`. This becomes a literal `typeInfo` value in the typed tree. Type: `typeInfo`.

**3. Switch on known value.** The scrutinee is a known variant `Record({fields: [...]})`. The type checker matches it against the case patterns:
- `String` — doesn't match, **skip this branch entirely** (never type-checked)
- `Int` — doesn't match, **skip**
- `Record({fields})` — matches! Type-check only this branch. Bind `fields` to the comptime-known array.

Skipping non-matching branches is critical — `Json.string(value)` where `value: user` would fail type checking. The type checker never sees it.

**4. `let obj = Dict.empty()`.** Normal runtime expression. Type-checked as usual. Emitted to typed tree.

**5. `inline for field in fields { body }`.** The type checker sees `Pexp_inline_for`. The collection `fields` is a comptime-known array with 3 elements. The type checker **unrolls**: it type-checks `body` three separate times with `field` bound to each element.

**6. Iteration 1: `field = {name: "name", typ: String}`**

- `field.name` — `field` is comptime-known → evaluates to `"name"` → `Texp_constant("name")`
- `@field(value, field.name)` → `@field(myUser, "name")` → validate "name" is a field of `user` (yes, type `string`) → produces `Texp_field(myUser, name)` with type `string`
- `encode(@field(value, field.name))` → recursive `@comptime` call! Inline `encode` with `value = myUser.name` (type: `string`)
  - `@typeInfo(value)` → type is `string` → produces `String` variant
  - Switch picks `String` branch → `Json.string(value)` → `Json.string(myUser.name)`
- `Dict.set(obj, "name", Json.string(myUser.name))` → emitted to typed tree

**7. Iteration 2: `field = {name: "age", typ: Int}`**

- `@field(myUser, "age")` → `Texp_field(myUser, age)` type `int`
- `encode(myUser.age)` → inline → `@typeInfo` → `Int` → picks Int branch → `Json.number(Int.toFloat(myUser.age))`
- Emit: `Dict.set(obj, "age", Json.number(Int.toFloat(myUser.age)))`

**8. Iteration 3: `field = {name: "address", typ: Record(address)}`**

- `@field(myUser, "address")` → `Texp_field(myUser, address)` type `address`
- `encode(myUser.address)` → inline → `@typeInfo` → `Record({fields: [street, city]})` → picks Record branch
  - `let obj$1 = Dict.empty()` → emitted
  - `inline for` over address fields → 2 iterations:
    - `Dict.set(obj$1, "street", Json.string(myUser.address.street))`
    - `Dict.set(obj$1, "city", Json.string(myUser.address.city))`
  - `Json.object_(obj$1)` → emitted
- Emit: `Dict.set(obj, "address", Json.object_(obj$1))`

**9. `Json.object_(obj)` → emitted.**

### Final typed tree (and resulting JS)

```javascript
let obj = Dict.empty();
Dict.set(obj, "name", Json.string(myUser.name));
Dict.set(obj, "age", Json.number(Int.toFloat(myUser.age)));
let obj$1 = Dict.empty();
Dict.set(obj$1, "street", Json.string(myUser.address.street));
Dict.set(obj$1, "city", Json.string(myUser.address.city));
Dict.set(obj, "address", Json.object_(obj$1));
let json = Json.object_(obj);
```

No type dispatch at runtime. Fully specialized. Nested records handled by recursive inlining.

## What `type_expect` Does Differently

These are NOT special comptime behaviors — they're general type checker capabilities that work everywhere:

| Expression | What the type checker does |
|---|---|
| `@typeInfo(value)` | Look up value's static type, build TypeInfo, return literal `typeInfo` value |
| `switch <known variant> { cases }` | Match the known value, type-check ONLY the matching branch, skip others |
| `inline for x in <known array> { body }` | Unroll: type-check body N times, once per element, with x bound |
| `@field(value, <known string>)` | Validate field exists on value's type, produce `Texp_field` with correct type |
| `f(arg)` where f is `@comptime` | Inline f's body, type-check with arg's concrete type |

The `@comptime` attribute's only job: **inline the function body at the call site** so the type checker sees concrete types instead of polymorphic parameters.

## Two Comptime Mechanisms

### `@comptime` — Specialization via Inlining

The function body is inlined at each call site. The type checker type-checks it with concrete types. `@typeInfo`, `@field`, `inline for` are builtins that the type checker handles. The optimizer folds switches on known values.

No JS engine. No special evaluation. Just inlining + builtins + optimization.

### `@comptime.inline` — Full Evaluation in JS Engine (Boa)

The ENTIRE function executes at compile time in Boa. All arguments must be comptime-known. The function is compiled to JS, executed, and the result is inlined as a constant.

```rescript
@comptime.inline
let capitalize = (s: string): string => {
  String.charAt(s, 0)->String.toUpperCase ++ String.sliceToEnd(s, ~start=1)
}
```

When called with a comptime-known argument (like `capitalize("name")` inside an `inline for`), Boa evaluates it to `"Name"` and the result is inlined as a constant.

If called with a runtime argument, the compiler emits an error.

### How they compose

```rescript
@comptime.inline
let capitalize = (s: string): string => { ... }

@comptime
let rec encode = (value) => {
  switch @typeInfo(value) {
  | Record({fields}) =>
    let obj = Dict.empty()
    inline for field in fields {
      Dict.set(obj, capitalize(field.name), encode(@field(value, field.name)))
      //            ^^^^^^^^^^^^^^^^^^^^^^
      //            field.name is comptime-known ("name") → Boa evaluates
      //            capitalize("name") → "Name" → inlined as constant
    }
    Json.object_(obj)
  }
}
```

## Lambda Switch Constant Folding ✅ DONE

When `Lswitch` scrutinee is a known constant, pick the matching branch directly:
- `Const_int(tag)` → look up in `sw_consts`
- `Const_block(tag)` → look up in `sw_blocks`

This was ~15 lines in `simplify.rs`. Now `switch Red { | Red => "red" | Green => "green" }` compiles to just `"red"`.

## Implementation Order

1. ✅ **Lambda switch constant folding** — done
2. **`typeInfo` as predefined type** — add to predef.rs/env.rs
3. **`@typeInfo(value)` in type checker** — look up value's type, construct literal typeInfo value
4. **Switch on known typeInfo** — type checker skips non-matching branches
5. **`inline for` unrolling** — type checker unrolls over known array
6. **`@field(value, name)` validation + generation** — validate field exists, produce Texp_field
7. **`@comptime` function inlining** — inline body at call site with concrete types
8. **Recursive specialization** — re-enter for nested types (fuel-limited)
9. **`@comptime.inline` + Boa** — for full compile-time evaluation of helper functions

Steps 2-8 are the core. Step 9 adds support for user-written comptime helpers.
