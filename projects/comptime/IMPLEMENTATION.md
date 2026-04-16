# Comptime Implementation Notes

## Architecture Decision: Let the Optimizer Do the Work

The comptime system relies on the ReScript compiler's existing optimization passes rather than building a separate interpreter. The key insight: if `@typeInfo(T)` expands to a **literal value** of a known type, the compiler's existing constant folding, dead branch elimination, and beta reduction handle the specialization automatically.

### How It Works

1. `@typeInfo(T)` is a compiler intrinsic that expands to a literal value (a variant constructor with payload)
2. The expanded value flows through the normal compilation pipeline
3. The optimizer folds switches on known values, eliminates dead branches, and propagates constants
4. The output is specialized code with no comptime residue

### Example

```rescript
@comptime
let encode = (comptime T: type, value: T): Json.t => {
  switch @typeInfo(T) {
  | Record({fields}) =>
    let obj = Dict.empty()
    inline for field in fields {
      Dict.set(obj, field.name, encode(field.typ, @field(value, field.name)))
    }
    Json.object_(obj)
  | String => Json.string(value)
  | Int => Json.number(Int.toFloat(value))
  | _ => @compileError(`Cannot encode ${@typeName(T)}`)
  }
}
```

When called as `encode(user, myUser)`, the compiler:

1. Expands `@typeInfo(user)` → `Record({name: "user", fields: [{name: "name", typ: String, ...}, {name: "age", typ: Int, ...}], unboxed: false})`
2. The switch scrutinee is now a known variant value
3. The optimizer picks the `Record` branch, eliminates all others
4. `inline for` unrolls over the known fields array
5. Each `field.name` folds to a string constant (`"name"`, `"age"`)
6. Recursive `encode(field.typ, ...)` calls specialize further (T=String picks the String branch, etc.)
7. `@field(value, field.name)` becomes `value.name` (a direct field access)
8. Result: flat, specialized code with no type dispatch

## Required Compiler Changes

### 1. Lambda Switch Constant Folding (MISSING)

**Current behavior:** `switch Red { | Red => "red" | Green => "green" }` does NOT fold. The lambda IR creates `let tmp = Const_int(0); Lswitch(tmp, ...)` and the switch is preserved at runtime.

**Required behavior:** When `Lswitch` scrutinee is a known `Lconst(Const_int(tag, _))`, look up `tag` in `sw_consts` and return the matching body directly. Same for `Const_block` in `sw_blocks`.

**Evidence that this is feasible:**
- String switches already fold: `switch "a" { | "a" => "yes" | _ => "no" }` → `"yes"` ✅
- Bool switches fold: `switch true { | true => "yes" | false => "no" }` → `"yes"` ✅
- Single-constructor variants with payloads fold: `switch B(42) { | B(n) => n }` → `42` ✅ (because pattern matching compiles to direct `Pfield` extraction, not `Lswitch`)
- Multi-way variant switches do NOT fold: `switch Red { | Red => "r" | Green => "g" }` → runtime switch ❌

**Fix location:** `compiler-rust/src/lambda/simplify.rs` in `simplify_with_env` for the `Lswitch` case. ~15 lines of code.

**Fix description:** When the scrutinee resolves to a known constant:
- `Lconst(Const_int(tag, _))` → look up `tag` in `sw_consts`, return matching body
- `Lconst(Const_block(tag, _, fields))` → look up `tag` in `sw_blocks`, substitute field accesses with known values

This is a general optimization that benefits ALL ReScript code, not just comptime.

### 2. `typeInfo` as a Predefined Type

Define `typeInfo`, `fieldInfo`, `constructorInfo` as predefined types (like `bool`, `option`) in `predef.rs` and `env.rs`. These types are available without imports and the compiler knows how to construct literal values of these types.

```rescript
// Predefined — no import needed
type rec typeInfo =
  | Int
  | Float
  | String
  | Bool
  | Unit
  | Char
  | Record({name: string, fields: array<fieldInfo>, unboxed: bool})
  | Variant({name: string, constructors: array<constructorInfo>, unboxed: bool})
  | Array({element: typeInfo})
  | Option({inner: typeInfo})
  | Function({args: array<typeInfo>, returnType: typeInfo})
  | Unknown
and fieldInfo = {
  name: string,
  typ: typeInfo,
  optional: bool,
  mutable_: bool,
}
and constructorInfo = {
  name: string,
  args: array<typeInfo>,
}
```

### 3. `@typeInfo(T)` Compiler Intrinsic

When the type checker encounters `Pexp_comptime_typeinfo(core_type)`:
1. Resolve `core_type` to a concrete type using the type context
2. Construct a literal value of type `typeInfo` (a typed tree `Texp_construct` node)
3. Return the literal expression

The literal is a real value that flows through the normal pipeline. The optimizer handles the rest.

### 4. `inline for` Unrolling

`inline for field in fields { body }` where `fields` is a known array literal:
1. Evaluate `fields` to get the array elements
2. For each element, clone `body` and substitute `field` with the element
3. Sequence the results with `Texp_sequence`

This requires the optimizer to propagate known array values and unroll the loop. If the array literal is known at compile time (which it is — it comes from `@typeInfo`), the compiler can unroll it during lambda simplification.

### 5. `@field(value, name)` Intrinsic

When `name` is a known string constant (from comptime evaluation):
1. Look up the field `name` in the type of `value`
2. Generate a `Texp_field` node (direct field access)

### 6. Recursive Comptime Calls

When `encode(field.typ, @field(value, field.name))` is encountered:
- `field.typ` is a known `typeInfo` value (e.g., `String`)
- The compiler inlines the `encode` body with `T = String`
- `@typeInfo(String)` expands to `String` (the variant)
- The switch picks the `String` branch
- Result: `Json.string(value.name)`

This is just the same mechanism applied recursively. Fuel limits prevent infinite recursion.

## What Does NOT Need a JS Interpreter

The entire encode/decode pattern works without Boa:
- Type resolution → Rust (reads from TypeContext)
- Switch elimination → compiler optimizer (constant folding on variants)
- Loop unrolling → compiler (inline for on known arrays)
- Field access → Rust (constructs Texp_field)
- Recursive specialization → compiler (re-applies the same mechanism)
- Runtime expressions → pass through unchanged

## What DOES Need a JS Interpreter (Future)

- Complex string manipulation: `capitalize(field.name)`, `String.concat(...)`
- User-written comptime helper functions: `parseGraphQL(query)`
- Array operations in comptime context: `fields->Array.filter(f => ...)`
- Any comptime expression that can't be constant-folded by the compiler

These are Phase 2. The core encode/decode/keyOf patterns work with just compiler optimizations.

## Implementation Order

1. **Lambda switch constant folding** — ~15 lines in simplify.rs, enables all variant-based comptime
2. **`typeInfo` as predefined type** — add to predef.rs/env.rs, define constructors
3. **`@typeInfo(T)` expansion** — construct literal typeInfo values in type checker
4. **Verify switches fold** — with typeInfo as a real value, switches should fold automatically
5. **`inline for` unrolling** — unroll loops over known array literals
6. **`@field(value, name)` expansion** — generate field access nodes
7. **Recursive specialization** — inline comptime function bodies at call sites

Steps 1-4 are the critical path. Once variant switch folding works and `@typeInfo` produces real values, the optimizer does most of the work.
