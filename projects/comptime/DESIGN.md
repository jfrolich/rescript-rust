# ReScript Comptime: Compile-Time Metaprogramming

This document describes a proposed compile-time execution system for ReScript, inspired by Zig's comptime feature. The goal is to enable powerful metaprogramming capabilities that can replace all current PPX use cases while being simpler to use and maintain.

## Table of Contents

1. [Overview](#overview)
2. [Design Goals](#design-goals)
3. [Core Concepts](#core-concepts)
4. [Type Introspection](#type-introspection)
5. [Execution Model: QuickJS](#execution-model-quickjs)
6. [Why an Integrated In-Process Compiler](#why-an-integrated-in-process-compiler)
7. [Derive Attributes](#derive-attributes)
8. [Replacing PPXs](#replacing-ppxs)
9. [Implementation Plan](#implementation-plan)
10. [Appendix: Zig Comptime Reference](#appendix-zig-comptime-reference)

---

## Overview

### What is Comptime?

Comptime (compile-time execution) allows regular ReScript code to execute during compilation. Unlike PPXs, which require writing OCaml code that manipulates the AST, comptime lets you write ReScript code that:

1. **Runs at compile time** when all inputs are known
2. **Introspects types** via `@typeInfo`
3. **Generates specialized code** based on type structure
4. **Parses strings** (for DSLs like GraphQL, SQL, CSS)

### Why Comptime Over PPXs?

| Aspect | PPXs | Comptime |
|--------|------|----------|
| **Language** | OCaml | ReScript |
| **Toolchain** | Separate OCaml build | Part of compiler |
| **Debugging** | Complex AST manipulation | Regular ReScript code |
| **Testing** | Requires special setup | Standard unit tests |
| **Community** | OCaml expertise needed | Any ReScript developer |
| **Maintenance** | AST changes break PPXs | Stable interface |

### Key Design Choice: Zig-Style Partial Evaluation

Unlike macro systems that generate code as strings or AST, comptime uses **partial evaluation**. You write a normal function, mark compile-time-known parameters, and the compiler specializes it:

```rescript
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
  | _ => @compileError("unsupported type")
  }
}

// Call site:
let json = encode(myUser)
```

The compiler evaluates the `switch @typeInfo(value)` at compile time using the known type at each call site, picks the matching branch, unrolls `inline for`, recursively specializes each `encode` call. What comes out is concrete code with no type dispatch:

```javascript
// Generated output — no runtime type info, no loops, no generics
// Since JSON.Encode.* are all %identity, they compile to nothing!
let dict = {};
dict["name"] = myUser.name;
dict["age"] = myUser.age;
let dict$1 = {};
dict$1["street"] = myUser.address.street;
dict$1["city"] = myUser.address.city;
dict["address"] = dict$1;
let json = dict;
```

No code generation step. No strings, no AST builders, no quasi-quotation. The function body **is** the template. Comptime evaluation **is** specialization.

---

## Design Goals

### 1. Same Language, No Code Generation

Unlike macro systems with separate DSLs or code-as-strings, comptime is just ReScript. You write what looks like a normal function. The compiler partially evaluates it. There is no "generate code" step — the function body contains both comptime and runtime expressions, and the compiler teases them apart.

### 2. No Global State

The Rust compiler is designed for concurrent compilation. Comptime must not introduce global state:

- Each compilation unit gets its own QuickJS instance
- Type contexts are passed explicitly
- No `static mut` or `thread_local!`

### 3. Hermetic Evaluation

Following Zig's design, comptime has no I/O:

- No file system access (except `@embedFile`)
- No network access
- No randomness
- Results are deterministic and cacheable

QuickJS starts with a blank global scope by default — no `fs`, `fetch`, `process`. Only the comptime builtins are exposed.

### 4. Explicit Opt-In

Code must be explicitly marked for compile-time evaluation:

```rescript
@comptime           // Function can run at comptime
let helper = ...

comptime T: type    // Parameter must be comptime-known
```

### 5. Fuel Limits

To prevent infinite loops from hanging the compiler:

```rust
const DEFAULT_FUEL: usize = 100_000;
```

Each interpreter step decrements fuel. Exhaustion produces a compile error.

### 6. Fully In-Memory

Comptime code is compiled to JS and executed in-memory during compilation. No comptime artifacts are written to disk. No comptime JS appears in the compiled output. Comptime functions do their job during compilation and disappear — only the specialized runtime code remains.

---

## Core Concepts

### Comptime Functions

Functions marked `@comptime` can execute at compile time when all comptime parameters are known:

```rescript
@comptime
let double = (comptime x: int): int => x * 2

let a = double(5)        // Comptime: becomes `let a = 10`
let b = double(runtime)  // Error: runtime is not comptime-known
```

### Comptime Parameters

Parameters marked `comptime` must be known at compile time. Non-comptime parameters become runtime code:

```rescript
@comptime
let encode = (comptime T: type, value: T): JSON.t => {
  switch @typeInfo(T) {
  | String => JSON.Encode.string(value)     // value is runtime
  | Int => JSON.Encode.int(value)
  | _ => @compileError(`Cannot encode ${@typeName(T)}`)
  }
}

let x = encode(string, myString)   // T is comptime, value is runtime
let y = encode('a, something)      // Error: 'a is not comptime-known
```

### Fully Resolved Types Required

Comptime type parameters must be fully resolved — no unresolved type variables:

```rescript
encode(user, myUser)              // Fine: user is concrete
encode(array<int>, myArr)         // Fine: fully resolved
encode(array<'a>, myArr)          // Error: 'a not comptime-known
encode(option<string>, myOpt)     // Fine: fully resolved

// Polymorphism and comptime are opposites:
// - Polymorphism: works for any type at runtime
// - Comptime: specialized for a specific type at compile time
```

### Inline For

Loops over comptime arrays are unrolled:

```rescript
@comptime
let fields = @typeInfo(user)->getFields

// This loop is unrolled at compile time
inline for field in fields {
  Console.log(field.name)
}

// Becomes:
Console.log("id")
Console.log("name")
Console.log("email")
```

### Comptime Types

Comptime functions (value → value) use `@comptime` on `let` bindings. For type-level computation (type → type), use `@comptime` on a type declaration:

```rescript
@comptime
type keyOf<'T> = {
  switch @typeInfo('T) {
  | Record({fields}) =>
    @buildVariant(inline for field in fields {
      @variantCase({name: field.name->String.capitalize, as: field.name})
    })
  | _ => @compileError("@keyOf requires a record type")
  }
}

type user = { name: string, age: int, email: string }
type user_key = keyOf<user>
// Produces:
// type user_key =
//   | @as("name") Name
//   | @as("age") Age
//   | @as("email") Email
```

The type parameter `'T` must be fully resolved at the call site — `keyOf<user>` works, `keyOf<'a>` is a compile error. This is consistent with comptime value functions: comptime parameters must be known at compile time.

**Two kinds of comptime, same model:**

| | Value-level | Type-level |
|---|---|---|
| **Syntax** | `@comptime let f = (comptime T: type, value: T) => ...` | `@comptime type f<'T> = ...` |
| **Input** | Comptime params + runtime values | Type parameters (must be concrete) |
| **Output** | Specialized runtime code | A new type declaration |
| **Usage** | `f(myType, myValue)` | `type t = f<myType>` |
| **Body** | Mix of comptime decisions + runtime expressions | Comptime only — type-building directives |

#### Type-Building Builtins

Comptime type bodies use these builtins to construct types:

**`@buildVariant`** — build a variant type from `@variantCase` entries:

```rescript
@buildVariant(
  @variantCase({name: "Active", as: "active"}),
  @variantCase({name: "Inactive"}),
  @variantCase({name: "Suspended", deprecated: "Use Inactive instead"}),
)
```

**`@variantCase`** — describe a single variant constructor. Takes a record:

```rescript
@variantCase({
  name: string,                          // required: constructor name
  as?: string,                           // @as("...") JS representation
  payload?: typeInfo,                    // constructor argument type(s)
  deprecated?: string,                  // @deprecated("...")
})
```

**`@buildRecord`** — build a record type from field descriptions:

```rescript
@buildRecord(inline for field in fields {
  @recordField({name: field.name, typ: field.typ, optional: true})
})
```

**`@recordField`** — describe a single record field:

```rescript
@recordField({
  name: string,                          // required: field name
  typ: typeInfo,                         // required: field type
  optional?: bool,                       // x?: int
  mutable_?: bool,                       // mutable x: int
  as?: string,                           // @as("userName")
})
```

---

## Type Introspection

### The typeInfo Representation

Types at compile time are represented as a variant. Since comptime requires fully resolved types, there are no unresolved type variables — the type info tree is always concrete.

```rescript
type rec typeInfo =
  // === Primitives ===
  | Int
  | Float
  | String
  | Char
  | Bool
  | Unit
  | Bigint

  // === Containers (always concrete element types) ===
  | Array({element: typeInfo})
  | Dict({value: typeInfo})
  | Option({inner: typeInfo})
  | Null({inner: typeInfo})
  | Nullable({inner: typeInfo})
  | Promise({value: typeInfo})
  | Tuple({elements: array<typeInfo>})

  // === Record ===
  | Record({
      name: string,
      modulePath: string,
      fields: array<fieldInfo>,
      attributes: array<attribute>,
      unboxed: bool,
    })

  // === Variant ===
  | Variant({
      name: string,
      modulePath: string,
      constructors: array<constructorInfo>,
      attributes: array<attribute>,
      unboxed: bool,
      tag: option<string>,              // @tag("kind") → Some("kind")
    })

  // === Polymorphic Variant ===
  | PolyVariant({
      cases: array<polyCase>,
      closed: bool,                     // [#A | #B] vs [> #A | #B]
    })

  // === Function ===
  | Function({
      args: array<argInfo>,
      return: typeInfo,
    })

  // === Object type ===
  | Object({
      methods: array<methodInfo>,
      open_: bool,                      // {..} vs {.}
    })

  // === Opaque (ReScript type, definition hidden by module signature) ===
  | Opaque({
      name: string,
      modulePath: string,
      attributes: array<attribute>,
    })

  // === External (JS interop type, no ReScript definition) ===
  | External({
      name: string,
      modulePath: string,              // "Js.Date", "Dom", "ReactDOM"
      attributes: array<attribute>,
      bindings: array<externalBinding>,
    })

  // === Alias (user-defined type alias) ===
  | Alias({
      name: string,
      modulePath: string,
      resolved: typeInfo,              // what it actually is
      attributes: array<attribute>,
    })

  // === Recursive reference (breaks cycles in recursive types) ===
  | Recursive({name: string, modulePath: string})
```

### Field Info

```rescript
and fieldInfo = {
  name: string,
  typ: typeInfo,
  mutable_: bool,
  optional: bool,                       // x?: int
  attributes: array<attribute>,
  jsName: string,                       // @as("userName") → "userName", else name
}
```

### Constructor Info

```rescript
and constructorInfo = {
  name: string,
  args: constructorArgs,
  attributes: array<attribute>,
  jsValue: option<constructorJsRepr>,
}

and constructorArgs =
  | NoArgs                              // | A
  | TupleArgs(array<typeInfo>)          // | A(int, string)
  | InlineRecord(array<fieldInfo>)      // | A({x: int, y: string})

and constructorJsRepr =
  | JsString(string)                    // @as("active")
  | JsInt(int)                          // @as(0)
  | JsBool(bool)                        // @as(true)
  | JsNull                              // @as(null)
  | JsUndefined                         // @as(undefined)
```

### Polymorphic Variant Case

```rescript
and polyCase = {
  name: string,                         // #A, #"some-name"
  payload: option<polyPayload>,
  attributes: array<attribute>,
  jsValue: option<constructorJsRepr>,
}

and polyPayload =
  | Single(typeInfo)                    // #A(int)
  | Multiple(array<typeInfo>)           // #A(int, string)
```

### Function Arg Info

```rescript
and argInfo = {
  label: argLabel,
  typ: typeInfo,
}

and argLabel =
  | Positional
  | Labeled(string)                     // ~name: string
  | Optional(string)                    // ~name: string=?
```

### Object Method Info

```rescript
and methodInfo = {
  name: string,
  typ: typeInfo,
}
```

### Attributes

```rescript
and attribute = {
  name: string,
  payload: option<string>,
}
```

### External Bindings (Sum Type)

External bindings represent JS interop declarations associated with an external type. Each binding is exactly one thing:

```rescript
and externalBinding =
  | Constructor({                       // @new external make: unit => t = "Date"
      name: string,
      jsName: string,
      args: array<argInfo>,
      return: typeInfo,
    })
  | Method({                            // @send external toISOString: t => string
      name: string,
      jsName: string,
      args: array<argInfo>,             // excluding self
      return: typeInfo,
    })
  | Getter({                            // @get external length: t => int = "length"
      name: string,
      jsName: string,
      typ: typeInfo,
    })
  | Setter({                            // @set external setName: (t, string) => unit
      name: string,
      jsName: string,
      typ: typeInfo,
    })
  | StaticMethod({                      // @scope("Date") @val external now: unit => float
      name: string,
      jsName: string,
      args: array<argInfo>,
      return: typeInfo,
    })
  | GlobalValue({                       // @val external document: t = "document"
      name: string,
      jsName: string,
    })
  | ModuleImport({                      // @module("moment") external moment: string => t
      name: string,
      jsName: string,
      from: string,
      args: array<argInfo>,
      return: typeInfo,
    })
```

### Opaque vs External

These are fundamentally different:

- **Opaque**: A ReScript type with a hidden definition. It *has* structure, you just can't see it from outside the module. If comptime runs *inside* the defining module, it sees through to the real type.
- **External**: A JS value with no ReScript definition at all. It has whatever shape JS gave it. The `bindings` field exposes what the compiler knows about its JS API.

```rescript
@comptime
let rec encodeField = (comptime T: type, value: T): JSON.t => {
  switch @typeInfo(T) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Record({fields}) => ...
  | Opaque(_) =>
    // There IS a definition, but it's hidden.
    @compileError(`${@typeName(T)} is opaque. Expose the type or add @encode.`)
  | External({bindings}) =>
    // JS type — try to find a serialization method
    let hasToJSON = bindings->Array.find(b =>
      switch b {
      | Method({jsName: "toJSON"}) => true
      | _ => false
      }
    )
    switch hasToJSON {
    | Some(Method(m)) => value->@send(m.jsName)
    | _ => @compileError(`${@typeName(T)} is external with no known serialization`)
    }
  | ...
  }
}
```

### Introspection Builtins

```rescript
@typeInfo(user)           // → Record({fields: [...], ...})
@typeName(user)           // → "user"
@getAttr(field, "json.key") // → option<string>
@field(value, field.name)   // → field access with comptime-known name
@compileError(msg)          // → emit compile error
@embedFile(path)            // → embed file contents as string
```

### Type Alias Resolution

Built-in aliases are always fully resolved:

```rescript
@typeInfo(Array.t<int>)   // → Array({element: Int})
@typeInfo(array<int>)     // → Array({element: Int})
// identical — Array.t is just an alias for array
```

User-defined aliases are resolved by default. The original alias name is available if needed but the common case is simple:

```rescript
type userId = string
type user = { id: userId, name: string }

@typeInfo(user).fields[0].typ   // → String (fully resolved)
```

### Recursive Types

```rescript
type rec tree = { value: int, children: array<tree> }

@typeInfo(tree)
// → Record({
//     name: "tree",
//     fields: [
//       {name: "value", typ: Int},
//       {name: "children", typ: Array({element: Recursive({name: "tree"})})},
//     ]
//   })
```

The `Recursive` case breaks the cycle. Call `@typeInfo` again on the referenced type to follow it.

---

## Execution Model: QuickJS

### Why QuickJS?

ReScript already compiles to JavaScript. Instead of writing a custom interpreter in Rust, comptime functions are compiled to JS through the normal pipeline and executed with QuickJS embedded in the compiler.

- **Small** (~200KB compiled into the Rust binary), no external dependencies
- **Blank global scope** by default — hermetic by design, only expose comptime builtins
- **ES2020** support — plenty for comptime workloads
- **No JIT needed** — comptime code is short-lived, evaluating type info and unrolling loops

### Architecture: Partial Evaluation

QuickJS doesn't produce code — it **makes decisions** that the compiler uses to specialize:

1. Compiler walks the `@comptime` function's AST
2. Hits `@typeInfo(T)` → evaluates via host function, gets type info
3. Hits `switch` on comptime value → QuickJS evaluates the scrutinee, compiler keeps only the matching branch
4. Hits `inline for` → QuickJS evaluates the array, compiler unrolls the loop
5. Hits `@getAttr(field, "json.key")` → QuickJS evaluates, returns the attribute value
6. Runtime expressions are kept as AST with comptime values substituted as constants

QuickJS handles **computation** (string parsing, attribute lookup, conditional logic). The compiler handles **specialization** (branch selection, loop unrolling, constant substitution, recursive inlining).

### In-Memory Compilation Flow

```
@comptime function source
    ↓ normal parse + type check
Typed AST
    ↓ compile to JS (in memory, never written to disk)
JS source string
    ↓ stored in CompiledModule.comptime_js
    ↓ (available for cross-module comptime calls)

When called with comptime-known arguments:
    ↓ load into QuickJS context
    ↓ execute — calls host functions for @typeInfo etc.
    ↓ returns decisions/values
    ↓ compiler specializes the original AST
Specialized AST (comptime parts resolved, runtime parts remain)
    ↓ type check (normal)
    ↓ Lambda lowering (normal)
    ↓ JS codegen (normal)
Output JS (no trace of comptime)
```

### Module State

Each compiled module carries comptime JS in memory alongside its normal compilation output:

```rust
struct CompiledModule {
    signature: ModuleSignature,              // types, for downstream type checking
    lambda: Lambda,                          // runtime code, for JS emission
    comptime_js: HashMap<String, String>,    // fn_name → JS source, in memory only
}
```

### Cross-Module Comptime

When `User.res` calls a comptime function from `Codec.res`:

1. `Codec.res` was already compiled (dependency order)
2. Its comptime JS is in memory in `CompiledModule.comptime_js`
3. Load into the QuickJS context via custom module loader
4. Execute — the call chain works naturally across modules

QuickJS's custom module loader resolves imports from the compiler's in-memory module map:

```rust
context.set_module_loader(|module_name| {
    compiled_modules.get(module_name)
        .map(|m| m.comptime_js_bundle())
});
```

### Host Functions

The compiler exposes these to QuickJS:

```rust
// Type introspection — reads from the compiler's type environment
__comptime_typeInfo(type_path)      // → JS object with type structure
__comptime_typeName(type_path)      // → string
__comptime_getAttr(field, name)     // → string | null
__comptime_compileError(msg)        // → throws, compiler catches as compile error
```

These cross the Rust-QuickJS FFI boundary. Rust's borrow checker ensures the type environment isn't mutated while QuickJS is reading it.

---

## Why an Integrated In-Process Compiler

Comptime could theoretically be built on a traditional batch compiler (like OCaml's `bsc`). But an integrated, in-process Rust compiler is fundamentally better suited for it. Here's why.

### Comptime Erases the Phase Distinction

A traditional compiler has rigid phases: Parse → Type Check → Lower → Codegen. Each phase completes fully before the next. Artifacts on disk are the boundaries.

Comptime **destroys this model.** When the compiler hits `@encoder` on a type:

1. Type checking must pause
2. Comptime code must execute — which requires type info from *this* and *other* modules
3. Comptime produces specialized code
4. That code must be type-checked
5. The newly type-checked code might trigger more comptime
6. Only then can type checking continue

This is not a pipeline. It's a **conversation** between compilation phases. An in-process compiler does it naturally — all the state is right there.

### In-Memory Module Graph

The in-process compiler holds the entire project in memory — all modules' types, signatures, comptime JS, the full dependency graph. This changes what's possible:

**Comptime dependency resolution is trivial.** When `User.res` hits `@encoder`, the compiler needs the comptime JS for `Spice.encoder`. It's already in memory — compiled earlier in dependency order. Just hand QuickJS a reference. No file lookup, no deserialization, no cache invalidation.

With a batch compiler, you'd need to serialize comptime JS to disk (a `.comptime` artifact), load it when needed, track a second dependency graph for comptime deps, and handle cache invalidation across packages. You're building a second build system inside the build system.

### Comptime Dependency Chains

```rescript
// Package: rescript-schema (comptime JSON schema parser)
@comptime
let parseJsonSchema = (input: string): Schema.t => { ... }

// Package: rescript-api-gen (depends on rescript-schema)
@comptime.derive("api")
let api = (comptime decl: typeDeclaration): ... => {
  let schema = @embedFile(@getAttr(decl, "schema"))
  let parsed = Schema.parseJsonSchema(schema)   // cross-package comptime call
  generateEndpoints(parsed, decl)
}

// User's code (depends on rescript-api-gen)
@api @schema("./openapi.json")
type endpoints
```

**In-process:** All comptime JS from the dependency chain is in memory. QuickJS loads and calls across packages naturally. The compiler knows the full dependency graph and invalidates precisely.

**Batch:** Each package compiled separately. Need a new artifact format, a resolver for comptime artifacts across packages, a dependency tracker that distinguishes comptime deps from runtime deps, and cross-package cache invalidation. Every piece is duplicated infrastructure.

### The Type Environment as a Live Query Engine

When comptime calls `@typeInfo(user)`, the compiler walks its in-memory type environment — arena-allocated, indexed access, no serialization. The query is a function call.

In a batch compiler, the type environment for other modules was serialized to `.cmi` and discarded. To answer `@typeInfo(User.user)` from `App.res`, you'd need to deserialize `.cmi` files back into queryable structures. And `.cmi` files are lossy — they contain signatures, not full internal representations. Attributes on fields, internal aliases, implementation details needed by comptime may not survive the round-trip.

### IDE Integration

Comptime-generated code needs to work seamlessly in the IDE:

```rescript
@encoder @decoder
type user = { name: string, age: int }

let json = encode_user(myUser)
//         ^^^^^^^^^^^
//         hover: (user) => JSON.t
//         go-to-def: → generated by @encoder (Spice.res:15)
```

**In-process compiler as LSP backend:** The compiler is a long-lived process with the full module graph, all comptime results, all provenance. When the user edits the `user` type, the compiler incrementally re-runs `@encoder`, updates types, pushes new diagnostics. One process, one source of truth.

**Batch compiler as LSP backend:** The LSP server shells out to `bsc`, reads `.cmi` files. Generated code provenance is lost. Go-to-definition through comptime requires a separate provenance database. Re-running comptime on edit means re-invoking the compiler and re-reading artifacts.

### Incremental Comptime Caching

The in-process compiler can cache comptime results with fine granularity:

```rust
struct ComptimeCache {
    // Key: hash of (comptime function identity + type declaration + attributes)
    // Value: specialized AST
    cache: HashMap<u64, Vec<StructureItem>>,
}
```

When a type hasn't changed and the derive function hasn't changed, skip re-evaluation entirely. Precise, minimal invalidation because the compiler has the full before/after state in memory.

### Concurrency

Each module gets its own `ComptimeEngine` with its own QuickJS instance. Rust's ownership model ensures no shared mutable state between compilation units. Independent modules can compile (and run comptime) in parallel.

### Rust-QuickJS FFI Safety

The comptime boundary between Rust and QuickJS is hot — every `@typeInfo` call crosses it. Rust's type system (lifetimes, borrow checker) ensures the type environment isn't mutated during QuickJS callbacks. OCaml's C FFI with QuickJS would require manual GC management (`CAMLparam`/`CAMLreturn` stubs) with no static enforcement.

### Summary

| | Batch Compiler | In-Process Rust Compiler |
|---|---|---|
| Phase interleaving | Serialize/deserialize workarounds | Natural — call between phases |
| Cross-module type queries | Deserialize .cmi, lossy | Direct memory access, full fidelity |
| Comptime dependency chains | Second artifact format + build system | Just the module graph |
| IDE integration | Re-run compiler, re-read artifacts | Live state, incremental updates |
| Caching | Disk-based, coarse | In-memory, per-derive granularity |
| Concurrency | GIL / subprocess-per-module | Threads with ownership |

---

## Derive Attributes

### Rust-Inspired Derives

Like Rust's `#[derive(Serialize, Deserialize)]`, ReScript comptime supports derive attributes on type declarations:

```rescript
@encoder @decoder
type user = {
  name: string,
  @json.key("user_age") age: int,
  email: option<string>,
}

// ↑ automatically generates encode_user and decode_user
```

### Defining a Derive Handler

A derive handler is a comptime function registered to an attribute name:

```rescript
@comptime.derive("encoder")
let encoder = (comptime T: type) => {
  (value: T): JSON.t => {
    switch @typeInfo(T) {
    | Record({fields}) =>
      let obj = Dict.make()
      inline for field in fields {
        let key = @getAttr(field, "json.key")->Option.getOr(field.name)
        Dict.set(obj, key, encodeField(field.typ, @field(value, field.name)))
      }
      JSON.Encode.object(obj)
    | _ => @compileError(`@encoder requires a record type`)
    }
  }
}

@comptime
let rec encodeField = (comptime T: type, value: T): JSON.t => {
  switch @typeInfo(T) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Float => JSON.Encode.float(value)
  | Bool => JSON.Encode.bool(value)
  | Option(inner) =>
    switch value {
    | Some(v) => encodeField(inner, v)
    | None => JSON.Null
    }
  | Array(elem) =>
    value->Array.map(v => encodeField(elem, v))->JSON.Encode.array
  | External({bindings}) =>
    switch bindings->Array.find(b =>
      switch b { | Method({jsName: "toJSON"}) => true | _ => false }
    ) {
    | Some(Method(m)) => value->@send(m.jsName)
    | _ => @compileError(`Cannot encode external type ${@typeName(T)}`)
    }
  | Opaque(_) =>
    @compileError(`${@typeName(T)} is opaque. Expose the type or add @encode attribute.`)
  | _ => @compileError(`Cannot encode ${@typeName(T)}`)
  }
}
```

### What the Compiler Does

When processing:

```rescript
@encoder @decoder
type user = { name: string, @json.key("user_age") age: int, email: option<string> }
```

1. Type check the `user` declaration normally
2. See `@encoder` attribute → look up the registered derive handler
3. Call the handler in QuickJS with `T = user`
4. Compiler specializes the result (partial evaluation resolves all comptime expressions)
5. Splice the specialized function in after the type declaration
6. Type check it normally
7. Repeat for `@decoder`

The user's file effectively becomes:

```rescript
type user = { name: string, @json.key("user_age") age: int, email: option<string> }

// generated by @encoder — fully specialized, no type dispatch at runtime
let encode_user = (value: user): JSON.t => {
  let obj = Dict.make()
  Dict.set(obj, "name", JSON.Encode.string(value.name))
  Dict.set(obj, "user_age", JSON.Encode.int(value.age))
  Dict.set(obj, "email", switch value.email {
    | Some(v) => JSON.Encode.string(v)
    | None => JSON.Null
  })
  JSON.Encode.object(obj)
}

// generated by @decoder
let decode_user = (json: JSON.t): result<user, string> => { ... }
```

### Decoder Example

```rescript
@comptime.derive("decoder")
let decoder = (comptime T: type) => {
  (json: JSON.t): result<T, string> => {
    switch @typeInfo(T) {
    | Record({fields}) =>
      switch JSON.Classify.classify(json) {
      | JSONObject(dict) =>
        inline for field in fields {
          let key = @getAttr(field, "json.key")->Option.getOr(field.name)
          let raw = Dict.get(dict, key)
          switch (raw, field.optional) {
          | (None, false) => return Error(`Missing field: ${key}`)
          | _ => ()
          }
        }
        // ... build record from decoded fields
      | _ => Error("Expected object")
      }
    | _ => @compileError(`@decoder requires a record type`)
    }
  }
}
```

### Registration (TBD)

How derive attributes are registered to handlers is an open design question. Options include:

- **Config-based:** `rescript.json` maps attribute names to handler modules
- **Convention-based:** `@encoder` looks for a module `Encoder` with a `@comptime.derive` export
- **Declaration-based:** `@comptime.derive("encoder")` self-registers when the module is compiled

The exact mechanism can be decided later. The important thing is: the user's experience is just `@encoder` on a type.

---

## Replacing PPXs

### Overview

Comptime can replace all current PPX use cases because:

1. **PPXs receive strings** via extension points
2. **Comptime can parse strings** at compile time
3. **Both generate code** based on the parsed/introspected information

### 1. JSON Serialization (ppx_spice, Decco)

**Current PPX:**
```rescript
@spice
type user = {
  name: string,
  @spice.key("user_age") age: int,
  email: option<string>,
}
// Generates: user_encode, user_decode
```

**With Comptime:**
```rescript
// Codec.res - Generic JSON codec generator
@comptime
let rec encodeField = (comptime T: type, value: T): JSON.t => {
  switch @typeInfo(T) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Float => JSON.Encode.float(value)
  | Bool => JSON.Encode.bool(value)
  | Option(inner) =>
    switch value {
    | Some(v) => encodeField(inner, v)
    | None => JSON.Null
    }
  | Array(elem) =>
    value->Array.map(v => encodeField(elem, v))->JSON.Encode.array
  | Record({fields}) =>
    let obj = Dict.make()
    inline for field in fields {
      let key = @getAttr(field, "json.key")->Option.getOr(field.name)
      Dict.set(obj, key, encodeField(field.typ, @field(value, field.name)))
    }
    JSON.Encode.object(obj)
  | External({bindings}) =>
    switch bindings->Array.find(b =>
      switch b { | Method({jsName: "toJSON"}) => true | _ => false }
    ) {
    | Some(_) => value->@send("toJSON")
    | None => @compileError(`Cannot encode external type ${@typeName(T)}`)
    }
  | Opaque(_) =>
    @compileError(`${@typeName(T)} is opaque. Expose the type or add @encode.`)
  | _ => @compileError(`Unsupported type for JSON encoding: ${@typeName(T)}`)
  }
}

@comptime.derive("encoder")
let encoder = (comptime T: type) => {
  (value: T): JSON.t => {
    switch @typeInfo(T) {
    | Record({fields}) =>
      let obj = Dict.make()
      inline for field in fields {
        let key = @getAttr(field, "json.key")->Option.getOr(field.name)
        Dict.set(obj, key, encodeField(field.typ, @field(value, field.name)))
      }
      JSON.Encode.object(obj)
    | _ => @compileError(`@encoder requires a record type`)
    }
  }
}

@comptime
let rec decodeField = (comptime T: type, json: JSON.t): result<T, string> => {
  switch @typeInfo(T) {
  | String =>
    switch JSON.Classify.classify(json) {
    | JSONString(s) => Ok(s)
    | _ => Error(`Expected string, got ${JSON.Encode.stringify(json)}`)
    }
  | Int =>
    switch JSON.Classify.classify(json) {
    | JSONNumber(n) => Ok(Int.fromFloat(n))
    | _ => Error(`Expected int`)
    }
  | Float =>
    switch JSON.Classify.classify(json) {
    | JSONNumber(n) => Ok(n)
    | _ => Error(`Expected float`)
    }
  | Bool =>
    switch JSON.Classify.classify(json) {
    | JSONTrue => Ok(true)
    | JSONFalse => Ok(false)
    | _ => Error(`Expected bool`)
    }
  | Option(inner) =>
    switch JSON.Classify.classify(json) {
    | JSONNull => Ok(None)
    | _ => decodeField(inner, json)->Result.map(v => Some(v))
    }
  | Array(elem) =>
    switch JSON.Classify.classify(json) {
    | JSONArray(arr) =>
      arr->Array.map(v => decodeField(elem, v))->Array.reduce(Ok([]), (acc, r) =>
        switch (acc, r) {
        | (Ok(arr), Ok(v)) => Ok(Array.concat(arr, [v]))
        | (Error(e), _) => Error(e)
        | (_, Error(e)) => Error(e)
        }
      )
    | _ => Error("Expected array")
    }
  | Record({fields}) =>
    switch JSON.Classify.classify(json) {
    | JSONObject(dict) =>
      inline for field in fields {
        let key = @getAttr(field, "json.key")->Option.getOr(field.name)
        let raw = Dict.get(dict, key)
        switch (raw, field.optional) {
        | (Some(v), _) =>
          switch decodeField(field.typ, v) {
          | Error(e) => return Error(`${field.name}: ${e}`)
          | Ok(_) => ()
          }
        | (None, true) => ()
        | (None, false) => return Error(`Missing field: ${key}`)
        }
      }
      Ok(@buildRecord(T))
    | _ => Error("Expected object")
    }
  | _ => @compileError(`Cannot decode ${@typeName(T)}`)
  }
}

// Usage
@encoder @decoder
type user = {
  name: string,
  @json.key("user_age") age: int,
  email: option<string>,
}

let json = encode_user({name: "Alice", age: 30, email: Some("alice@example.com")})
let user = decode_user(json)
```

### 2. GraphQL (graphql-ppx, rescript-relay)

**Current PPX:**
```rescript
module UserQuery = %graphql(`
  query UserQuery($id: ID!) {
    user(id: $id) {
      id
      name
      email
    }
  }
`)
```

**With Comptime:**
```rescript
// graphql/parser.res - GraphQL parser written in ReScript, runs in QuickJS

type token =
  | LBrace | RBrace | LParen | RParen | Colon | Bang | Dollar
  | Name(string) | StringLit(string) | IntLit(int)

type graphqlType =
  | Named(string)
  | NonNull(graphqlType)
  | List(graphqlType)

type variable = {name: string, typ: graphqlType}
type field = {name: string, alias: option<string>, args: array<argument>, selectionSet: array<field>}
and argument = {name: string, value: argumentValue}
and argumentValue = Variable(string) | StringValue(string) | IntValue(int) | BoolValue(bool)

type operation = {
  kind: [#query | #mutation | #subscription],
  name: option<string>,
  variables: array<variable>,
  selectionSet: array<field>,
}

@comptime
let tokenize = (comptime input: string): array<token> => {
  let tokens = []
  let i = ref(0)
  let len = String.length(input)

  while i.contents < len {
    let c = String.get(input, i.contents)
    switch c {
    | '{' => { Array.push(tokens, LBrace); i := i.contents + 1 }
    | '}' => { Array.push(tokens, RBrace); i := i.contents + 1 }
    | '(' => { Array.push(tokens, LParen); i := i.contents + 1 }
    | ')' => { Array.push(tokens, RParen); i := i.contents + 1 }
    | ':' => { Array.push(tokens, Colon); i := i.contents + 1 }
    | '!' => { Array.push(tokens, Bang); i := i.contents + 1 }
    | '$' => { Array.push(tokens, Dollar); i := i.contents + 1 }
    | ' ' | '\n' | '\t' | '\r' | ',' => i := i.contents + 1
    | '#' => {
      while i.contents < len && String.get(input, i.contents) != '\n' {
        i := i.contents + 1
      }
    }
    | 'a'..'z' | 'A'..'Z' | '_' => {
      let start = i.contents
      while i.contents < len {
        let ch = String.get(input, i.contents)
        switch ch {
        | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' => i := i.contents + 1
        | _ => break
        }
      }
      Array.push(tokens, Name(String.sub(input, start, i.contents - start)))
    }
    | '"' => {
      i := i.contents + 1
      let start = i.contents
      while i.contents < len && String.get(input, i.contents) != '"' {
        i := i.contents + 1
      }
      Array.push(tokens, StringLit(String.sub(input, start, i.contents - start)))
      i := i.contents + 1
    }
    | '0'..'9' => {
      let start = i.contents
      while i.contents < len {
        let ch = String.get(input, i.contents)
        switch ch {
        | '0'..'9' => i := i.contents + 1
        | _ => break
        }
      }
      Array.push(tokens, IntLit(Int.fromString(String.sub(input, start, i.contents - start))->Option.getExn))
    }
    | _ => @compileError(`Unexpected character in GraphQL: '${String.make(1, c)}'`)
    }
  }
  tokens
}

@comptime
let parse = (comptime tokens: array<token>): operation => {
  let pos = ref(0)

  let peek = () => tokens[pos.contents]
  let advance = () => { pos := pos.contents + 1 }
  let expect = (expected: token) => {
    if peek() != expected {
      @compileError(`Expected ${tokenToString(expected)}, got ${tokenToString(peek())}`)
    }
    advance()
  }

  let kind = switch peek() {
  | Name("query") => { advance(); #query }
  | Name("mutation") => { advance(); #mutation }
  | Name("subscription") => { advance(); #subscription }
  | _ => #query
  }

  let name = switch peek() {
  | Name(n) if n != "query" && n != "mutation" => { advance(); Some(n) }
  | _ => None
  }

  let variables = switch peek() {
  | LParen => {
    advance()
    let vars = []
    while peek() != RParen {
      expect(Dollar)
      let varName = switch peek() {
      | Name(n) => { advance(); n }
      | _ => @compileError("Expected variable name")
      }
      expect(Colon)
      let varType = parseType(tokens, pos)
      Array.push(vars, {name: varName, typ: varType})
    }
    expect(RParen)
    vars
  }
  | _ => []
  }

  expect(LBrace)
  let selectionSet = parseSelectionSet(tokens, pos)
  expect(RBrace)

  {kind, name, variables, selectionSet}
}

// graphql/codegen.res - Type generation from parsed query
@comptime
let graphql = (comptime query: string) => {
  let tokens = GraphQL.Parser.tokenize(query)
  let operation = GraphQL.Parser.parse(tokens)
  GraphQL.Validator.validate(operation, Schema.schema)
  GraphQL.Codegen.generateTypes(operation, Schema.schema)
}

// Usage
module UserQuery = graphql(`
  query UserQuery($id: ID!) {
    user(id: $id) {
      id
      name
      email
    }
  }
`)

// Generated types available:
// UserQuery.Variables = {id: string}
// UserQuery.Response = {user: {id: string, name: string, email: option<string>}}
// UserQuery.query = "query UserQuery($id: ID!) { ... }"
```

### 3. CSS-in-JS (styled-ppx)

**Current PPX:**
```rescript
module Button = %styled.button(`
  background-color: blue;
  padding: 10px 20px;
  &:hover {
    background-color: darkblue;
  }
`)
```

**With Comptime:**
```rescript
// css/parser.res - CSS parser

type cssValue =
  | Keyword(string)
  | Length(float, string)  // 10px, 2em, etc.
  | Color(string)
  | Number(float)

type cssRule = {
  property: string,
  value: cssValue,
}

type cssBlock = {
  selector: string,
  rules: array<cssRule>,
  nested: array<cssBlock>,
}

@comptime
let parseCSS = (comptime input: string): cssBlock => {
  let tokens = tokenizeCSS(input)
  parseCSSBlock(tokens, "&")
}

@comptime
let tokenizeCSS = (comptime input: string): array<cssToken> => {
  let tokens = []
  let i = ref(0)
  let len = String.length(input)

  while i.contents < len {
    let c = String.get(input, i.contents)
    switch c {
    | '{' => { Array.push(tokens, LBrace); i := i.contents + 1 }
    | '}' => { Array.push(tokens, RBrace); i := i.contents + 1 }
    | ':' => { Array.push(tokens, Colon); i := i.contents + 1 }
    | ';' => { Array.push(tokens, Semi); i := i.contents + 1 }
    | ' ' | '\n' | '\t' => i := i.contents + 1
    | '-' | 'a'..'z' | 'A'..'Z' => {
      let start = i.contents
      while i.contents < len {
        let ch = String.get(input, i.contents)
        switch ch {
        | 'a'..'z' | 'A'..'Z' | '0'..'9' | '-' | '_' => i := i.contents + 1
        | _ => break
        }
      }
      Array.push(tokens, Ident(String.sub(input, start, i.contents - start)))
    }
    | '0'..'9' | '.' => {
      let start = i.contents
      while i.contents < len {
        let ch = String.get(input, i.contents)
        switch ch {
        | '0'..'9' | '.' => i := i.contents + 1
        | _ => break
        }
      }
      let numStr = String.sub(input, start, i.contents - start)
      let unitStart = i.contents
      while i.contents < len {
        let ch = String.get(input, i.contents)
        switch ch {
        | 'a'..'z' | '%' => i := i.contents + 1
        | _ => break
        }
      }
      let unit = String.sub(input, unitStart, i.contents - unitStart)
      Array.push(tokens, Dimension(Float.fromString(numStr)->Option.getExn, unit))
    }
    | '#' => {
      i := i.contents + 1
      let start = i.contents
      while i.contents < len {
        let ch = String.get(input, i.contents)
        switch ch {
        | '0'..'9' | 'a'..'f' | 'A'..'F' => i := i.contents + 1
        | _ => break
        }
      }
      Array.push(tokens, Hash(String.sub(input, start, i.contents - start)))
    }
    | '&' => { Array.push(tokens, Ampersand); i := i.contents + 1 }
    | _ => i := i.contents + 1
    }
  }
  tokens
}

// css/validator.res - CSS property validation

let validProperties = [
  "background-color", "color", "padding", "margin", "width", "height",
  "display", "flex", "border", "font-size", "font-weight", // ...
]

@comptime
let validateCSS = (comptime block: cssBlock): unit => {
  block.rules->Array.forEach(rule => {
    if !Array.includes(validProperties, rule.property) {
      @compileError(`Unknown CSS property: ${rule.property}`)
    }
  })
  block.nested->Array.forEach(validateCSS)
}

// css/styled.res - Generate Emotion styles

@comptime
let generateClassName = (comptime css: string): string => {
  let hash = hashString(css)
  `css-${hash}`
}

@comptime
let styled = (comptime tag: string, comptime css: string) => {
  let block = CSS.Parser.parseCSS(css)
  CSS.Validator.validateCSS(block)

  let className = generateClassName(css)
  let cssString = CSS.Printer.print(block)

  // Inject CSS at module load time
  @sideEffect
  Emotion.injectGlobal(`.${className} { ${cssString} }`)

  // Return component
  React.forwardRef((props, ref) => {
    React.createElement(
      tag,
      {
        ...props,
        className: className,
        ref: ref,
      }
    )
  })
}

// Usage
let Button = styled("button", `
  background-color: blue;
  padding: 10px 20px;
  &:hover {
    background-color: darkblue;
  }
`)

// Usage in JSX
<Button onClick={handleClick}> {React.string("Click me")} </Button>
```

### 4. SQL (rescript-embed-lang)

**Current approach:**
```rescript
let findMovie = %sql.one(`SELECT id, title FROM movies WHERE id = $id`)
```

**With Comptime:**
```rescript
// sql/parser.res - SQL parser

type sqlExpr =
  | Column(string)
  | Param(string)
  | Literal(literal)
  | BinOp(sqlExpr, binOp, sqlExpr)

type selectQuery = {
  columns: array<selectColumn>,
  from: string,
  where: option<sqlExpr>,
  orderBy: array<(string, [#asc | #desc])>,
  limit: option<int>,
}

@comptime
let parseSQL = (comptime input: string): sqlQuery => {
  let tokens = tokenizeSQL(input)
  parseSQLQuery(tokens)
}

// sql/codegen.res - Type generation

@comptime
let sql = (comptime query: string, comptime schema: DBSchema) => {
  let parsed = SQL.Parser.parseSQL(query)

  // Extract parameters ($id, $name, etc.)
  let params = extractParams(parsed)

  // Infer column types from schema
  let columns = switch parsed {
  | Select(q) => q.columns->Array.map(col => {
      let table = schema.tables->Array.find(t => t.name == q.from)->Option.getExn
      let column = table.columns->Array.find(c => c.name == col.name)->Option.getExn
      {name: col.alias->Option.getOr(col.name), typ: column.typ}
    })
  | _ => []
  }

  {
    query: query,
    execute: (db, params) => db.query(query, params),
  }
}

// Usage
let findMovie = sql(
  `SELECT id, title FROM movies WHERE id = $id`,
  MovieDB.schema
)

// Type-safe usage:
let movie = await findMovie.execute(db, {id: "123"})
// movie: {id: string, title: string}
```

### 5. TypeScript Binding Helpers (ppx_ts)

**Current PPX:**
```rescript
@ppx_ts.keyOf
type config = {
  host: string,
  port: int,
}
// Generates: type config_keyOf = Host | Port
```

**With Comptime:**
```rescript
@comptime.derive("keyOf")
let keyOf = (comptime T: type) => {
  switch @typeInfo(T) {
  | Record({fields}) =>
    inline for field in fields {
      | @variant(String.capitalize(field.name))
    }
  | _ => @compileError("keyOf requires a record type")
  }
}

@comptime.derive("keyToString")
let keyToString = (comptime T: type) => {
  let keyType = keyOf(T)
  (key: keyType): string => {
    switch key {
    inline for field in @typeInfo(T)->getFields {
    | @variant(String.capitalize(field.name)) => field.name
    }
    }
  }
}

// Usage
@keyOf
type config = {
  host: string,
  port: int,
}

// Generated: type config_key = Host | Port
// Generated: let config_keyToString = ...

let key: config_key = Host
Console.log(config_keyToString(key))  // "host"
```

### 6. Form Bindings (ppx_react_hook_form)

**With Comptime:**
```rescript
@comptime.derive("form")
let makeForm = (comptime T: type) => {
  switch @typeInfo(T) {
  | Record({fields}) =>
    {
      useForm: () => {
        let form = ReactHookForm.useForm()

        inline for field in fields {
          let register = form.register(field.name)
        }

        form
      },

      // Type-safe field accessors
      fields: inline for field in fields {
        @record(field.name, FormField(field.typ))
      },
    }
  | _ => @compileError("@form requires a record type")
  }
}

// Usage
@form
type loginForm = {
  email: string,
  password: string,
  rememberMe: bool,
}

// Generated: LoginForm module with useForm() and typed fields

@react.component
let make = () => {
  let form = LoginForm.useForm()

  <form onSubmit={form.handleSubmit(data => Console.log(data))}>
    <input {...form.fields.email.register()} />
    <input {...form.fields.password.register()} type_="password" />
    <input {...form.fields.rememberMe.register()} type_="checkbox" />
    <button type_="submit"> {React.string("Login")} </button>
  </form>
}
```

---

## Examples

### Complete Example: Type-Safe API Client

```rescript
// api/schema.res - API schema definition
type endpoint<'params, 'response> = {
  method: [#GET | #POST | #PUT | #DELETE],
  path: string,
  params: 'params,
  response: 'response,
}

type user = {
  id: string,
  name: string,
  email: string,
}

type createUserParams = {
  name: string,
  email: string,
}

// api/client.res - Client generator
@comptime
let makeClient = (comptime endpoints: array<(string, endpoint<'p, 'r>)>) => {
  inline for (name, ep) in endpoints {
    @record(name, (ep.params) => {
      fetch(ep.path, {
        method: ep.method,
        body: Json.stringify(ep.params),
      })
    })
  }
}

// api/endpoints.res - Define endpoints
let endpoints = [
  ("getUser", {
    method: #GET,
    path: "/users/:id",
    params: type {id: string},
    response: type user,
  }),
  ("createUser", {
    method: #POST,
    path: "/users",
    params: type createUserParams,
    response: type user,
  }),
  ("deleteUser", {
    method: #DELETE,
    path: "/users/:id",
    params: type {id: string},
    response: type {success: bool},
  }),
]

// Usage
let client = makeClient(endpoints)

// Fully typed!
let user = await client.getUser({id: "123"})
let newUser = await client.createUser({name: "Alice", email: "alice@example.com"})
let result = await client.deleteUser({id: "123"})
```

### Complete Example: ORM Query Builder

```rescript
// orm/schema.res
type column<'t> = {
  name: string,
  typ: 't,
  nullable: bool,
  primaryKey: bool,
}

type table<'row> = {
  name: string,
  columns: array<column<_>>,
}

// orm/query.res
@comptime
let makeTable = (comptime name: string, comptime T: type): table<T> => {
  switch @typeInfo(T) {
  | Record({fields}) =>
    {
      name: name,
      columns: fields->Array.map(f => {
        name: f.name,
        typ: f.typ,
        nullable: f.optional,
        primaryKey: @hasAttr(f, "primaryKey"),
      }),
    }
  | _ => @compileError("Table row must be a record type")
  }
}

@comptime
let select = (comptime table: table<'row>) => {
  {
    from: table.name,
    columns: All,
    where: None,
    orderBy: [],
    limit: None,

    where: (condition) => { ...self, where: Some(condition) },
    orderBy: (column, dir) => { ...self, orderBy: [...self.orderBy, (column, dir)] },
    limit: (n) => { ...self, limit: Some(n) },

    execute: async (db) => {
      let sql = buildSQL(self)
      let rows = await db.query(sql)
      rows->Array.map(row => parseRow(row, table))
    },
  }
}

// Usage
type user = {
  @primaryKey id: string,
  name: string,
  email: option<string>,
  createdAt: Date.t,
}

let Users = makeTable("users", user)

let activeUsers = await
  select(Users)
  ->where(u => u.createdAt > Date.now() - days(30))
  ->orderBy("createdAt", #desc)
  ->limit(10)
  ->execute(db)

// activeUsers: array<user>
```

---

## Implementation Plan

### Phase 1: Core Infrastructure

**Goal:** QuickJS integration, basic comptime evaluation

1. Embed QuickJS in the Rust compiler via `rquickjs`
2. Add `@comptime` attribute parsing
3. Compile `@comptime` functions to JS (in memory)
4. Implement comptime parameter detection and specialization
5. Add fuel limits and error handling
6. Implement basic partial evaluation (switch on comptime values, constant substitution)

### Phase 2: Type Introspection

**Goal:** Enable `@typeInfo` and related builtins

1. Define the full `typeInfo` type in Rust
2. Implement `typeInfo` conversion from compiler internals
3. Register `__comptime_typeInfo` as QuickJS host function
4. Implement `@typeName`, `@getAttr`, `@field`, `@compileError`
5. Handle Opaque vs External distinction
6. Expose external binding info

### Phase 3: Partial Evaluation

**Goal:** Zig-style specialization

1. Implement `inline for` loop unrolling
2. Implement switch branch elimination on comptime values
3. Implement recursive comptime specialization
4. Implement constant inlining from comptime results
5. Splice specialized AST back into module structure

### Phase 4: Derive System

**Goal:** Attribute-triggered comptime

1. Implement `@comptime.derive` registration
2. Implement derive invocation at type declaration boundaries
3. Declaration-level interleaving (pause type checking → run comptime → splice → resume)
4. Cross-module comptime (load comptime JS from in-memory module graph)
5. Error reporting with comptime provenance

### Phase 5: Standard Library & Tooling

**Goal:** Practical comptime libraries and IDE support

1. JSON codec generator (encoder/decoder)
2. Parser utilities for DSLs
3. LSP support for comptime-generated code (hover, go-to-def, provenance)
4. Comptime result caching

---

## Appendix: Zig Comptime Reference

### How Zig Does It

Zig's compiler uses a multi-stage pipeline:

1. **AST → ZIR**: Source is parsed into Zig Intermediate Representation
2. **ZIR → AIR**: Semantic analysis transforms ZIR to Analyzed IR
3. **Comptime evaluation happens in Sema** (step 2)

The Sema phase attempts to evaluate each instruction:
- If operands are comptime-known → evaluate immediately
- If runtime values needed → generate AIR instructions

Zig explicitly chose to build a self-hosted compiler (abandoning the C++ bootstrap) because comptime needed deep integration with the compilation pipeline. The C++ bootstrap had limited comptime support. The self-hosted compiler made comptime first-class.

### Key Zig Features

```zig
// comptime keyword forces compile-time evaluation
const len = comptime multiply(4, 5);  // 20

// comptime parameters
fn Vec(comptime T: type, comptime N: usize) type {
    return struct {
        data: [N]T,
    };
}

// Type introspection
fn dump(value: anytype) void {
    const T = @TypeOf(value);
    switch (@typeInfo(T)) {
        .Int => std.debug.print("int: {}", .{value}),
        .Struct => |s| {
            inline for (s.fields) |field| {
                std.debug.print("{}: {}\n", .{field.name, @field(value, field.name)});
            }
        },
    }
}

// inline for - unrolled at comptime
inline for (fields) |field| {
    // Generates separate code for each field
}
```

### Why Template Haskell and Rust Proc Macros Are Painful

Both are comptime-like features bolted onto batch compilers:

**Rust proc macros** must live in a separate crate, compiled to a dylib. They only see token streams — no type information. This isn't a design choice, it's an architectural limitation: proc macros run before type checking.

**Template Haskell** has a "stage restriction" — a splice can't reference definitions from the same module that appear after it. GHC processes the file in chunks separated by splices. Cross-module TH requires the dependency to be fully compiled first.

Both systems are widely considered the most painful parts of their respective ecosystems. The pain comes from the architecture, not from bad design. ReScript's comptime avoids these pitfalls by being integrated into the compiler's compilation model.

### References

- [Zig Comptime Guide](https://zig.guide/language-basics/comptime/)
- [What is Zig's Comptime?](https://kristoff.it/blog/what-is-zig-comptime/)
- [Things Zig comptime Won't Do](https://matklad.github.io/2025/04/19/things-zig-comptime-wont-do.html)
- [Comptime Zig ORM](https://matklad.github.io/2025/03/19/comptime-zig-orm.html)
- [Zig Sema: ZIR → AIR](https://mitchellh.com/zig/sema)
