# Comptime Examples: Replacing PPXs

Concrete examples showing how comptime replaces every major PPX use case. Each section shows the current PPX pain, the full comptime implementation, and what the compiler produces.

---

## 1. JSON Codec (replaces `ppx_spice` / `Decco`)

### Comptime library

```rescript
// === Codec.res — reusable library, written in ReScript, not OCaml ===

@comptime
let rec encodeField = (comptime T: type, value: T): JSON.t => {
  switch @typeInfo(T) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Float => JSON.Encode.float(value)
  | Bool => JSON.Encode.bool(value)
  | Option({inner}) =>
    switch value {
    | Some(v) => encodeField(inner, v)
    | None => JSON.Null
    }
  | Array({element}) =>
    value->Array.map(v => encodeField(element, v))->JSON.Encode.array
  | Record({fields}) =>
    let obj = Dict.make()
    inline for field in fields {
      let key = @getAttr(field, "json.key")->Option.getOr(field.jsName)
      if field.optional {
        switch @field(value, field.name) {
        | Some(v) => Dict.set(obj, key, encodeField(field.typ, v))
        | None => ()
        }
      } else {
        Dict.set(obj, key, encodeField(field.typ, @field(value, field.name)))
      }
    }
    JSON.Encode.object(obj)
  | Variant({constructors, tag}) =>
    let tagKey = tag->Option.getOr("TAG")
    inline for ctor in constructors {
      switch value {
      | @variant(ctor.name) =>
        let obj = Dict.make()
        Dict.set(obj, tagKey, JSON.Encode.string(ctor.name))
        switch ctor.args {
        | NoArgs => ()
        | InlineRecord(fields) =>
          inline for f in fields {
            Dict.set(obj, f.name, encodeField(f.typ, @ctorField(value, ctor.name, f.name)))
          }
        | TupleArgs(args) =>
          inline for (i, arg) in Array.withIndex(args) {
            Dict.set(obj, `_${Int.toString(i)}`, encodeField(arg, @ctorArg(value, ctor.name, i)))
          }
        }
        JSON.Encode.object(obj)
      }
    }
  | Recursive(_) => @callEncoder(T, value)
  | _ => @compileError(`Cannot encode ${@typeName(T)}`)
  }
}

@comptime.derive("encoder")
let encoder = (comptime T: type) => {
  (value: T): JSON.t => encodeField(T, value)
}

@comptime.derive("decoder")
let decoder = (comptime T: type) => {
  (json: JSON.t): result<T, string> => decodeField(T, json, "$")
}
```

### Usage

```rescript
@encoder @decoder
type address = {
  street: string,
  city: string,
  @json.key("zip_code") zip: string,
}

@encoder @decoder
type user = {
  name: string,
  @json.key("user_age") age: int,
  email: option<string>,
  address: address,
  tags: array<string>,
}

let json = encode_user(myUser)
let result = decode_user(json)  // result<user, string> with path-aware errors
```

### What the compiler emits (no generics, no runtime dispatch)

```javascript
function encode_user(value) {
  var obj = {};
  obj["name"] = value.name;
  obj["user_age"] = value.age;
  if (value.email !== undefined) obj["email"] = value.email;
  var addr = {};
  addr["street"] = value.address.street;
  addr["city"] = value.address.city;
  addr["zip_code"] = value.address.zip;
  obj["address"] = addr;
  obj["tags"] = value.tags;
  return obj;
}
```

### Recursive types work naturally

```rescript
@encoder @decoder
type rec treeNode = {
  value: string,
  children: array<treeNode>,
}

// Compiler sees Recursive({name: "treeNode"}) and generates self-referencing call:
let rec encode_treeNode = (value: treeNode): JSON.t => {
  let obj = Dict.make()
  Dict.set(obj, "value", JSON.Encode.string(value.value))
  Dict.set(obj, "children",
    value.children->Array.map(v => encode_treeNode(v))->JSON.Encode.array
  )
  JSON.Encode.object(obj)
}
```

### Variant encoding

```rescript
@encoder @decoder
type shape =
  | Circle({radius: float})
  | Rectangle({width: float, height: float})
  | Point

// Generated:
let encode_shape = (value: shape): JSON.t => {
  switch value {
  | Circle({radius}) =>
    let obj = Dict.make()
    Dict.set(obj, "TAG", JSON.Encode.string("Circle"))
    Dict.set(obj, "radius", JSON.Encode.float(radius))
    JSON.Encode.object(obj)
  | Rectangle({width, height}) =>
    let obj = Dict.make()
    Dict.set(obj, "TAG", JSON.Encode.string("Rectangle"))
    Dict.set(obj, "width", JSON.Encode.float(width))
    Dict.set(obj, "height", JSON.Encode.float(height))
    JSON.Encode.object(obj)
  | Point =>
    let obj = Dict.make()
    Dict.set(obj, "TAG", JSON.Encode.string("Point"))
    JSON.Encode.object(obj)
  }
}
```

---

## 2. GraphQL (replaces `graphql-ppx` / `rescript-relay`)

### Comptime library

```rescript
// === GraphQL.res — parser + codegen + schema validation, all in ReScript ===

@comptime
let graphql = (comptime query: string, comptime schema: Schema.t) => {
  // Parse the query string at compile time
  let operation = Parser.parse(query)

  // Validate against schema — unknown fields become compile errors
  Validator.validate(operation, schema)
  // e.g. @compileError(`Field "nmae" not found on type "User". Did you mean "name"?`)

  // Generate typed module
  {
    // The query string itself (for sending to the server)
    query: query,

    // Type-safe variables constructor
    makeVariables: inline for v in operation.variables {
      @record(v.name, scalarToRescript(v.typ))
    },

    // Response type derived from schema + selection set
    parseResponse: (json: JSON.t) => {
      inline for field in operation.selectionSet {
        let schemaField = Schema.lookupField(schema, operation.rootType, field.name)
        @record(
          field.alias->Option.getOr(field.name),
          decodeGraphqlField(schemaField.typ, field, schema, json)
        )
      }
    },
  }
}
```

### Usage

```rescript
// Schema loaded at compile time from introspection JSON
@comptime let schema = GraphQL.Schema.load(@embedFile("./schema.graphql.json"))

module UserQuery = GraphQL.graphql(`
  query UserQuery($id: ID!) {
    user(id: $id) {
      id
      name
      email
      posts(first: 10) {
        title
        createdAt
      }
    }
  }
`, schema)

// Fully typed — typo in field name = compile error
let response = await fetch("/graphql", {
  method: "POST",
  body: Json.stringify({
    "query": UserQuery.query,
    "variables": UserQuery.makeVariables(~id="123"),
  }),
})
let data = UserQuery.parseResponse(await response.json())
// data.user.name: string
// data.user.posts: array<{title: string, createdAt: string}>
```

The GraphQL parser, validator, and codegen are all ReScript. Anyone can read, debug, and contribute. Schema validation errors are compile errors with good messages, not cryptic PPX crashes.

---

## 3. CSS-in-JS (replaces `styled-ppx`)

### Comptime library

```rescript
// === CSS.res — parser + validator ===

@comptime
let styled = (comptime tag: string, comptime css: string) => {
  // Parse CSS at compile time
  let block = Parser.parse(css)

  // Validate property names — compile error on typos
  inline for rule in block.rules {
    if !isValidProperty(rule.property) {
      @compileError(`Unknown CSS property "${rule.property}". Did you mean "${suggestProperty(rule.property)}"?`)
    }
  }

  // Generate deterministic class name from content hash
  let className = `css-${hashString(css)}`
  let cssString = Printer.print(block, className)

  // Runtime: inject stylesheet + return component
  @sideEffect Emotion.injectGlobal(cssString)

  React.forwardRef((props, ref) => {
    ReactDOM.createElement(tag, {
      ...props,
      className: switch props.className {
      | Some(c) => `${className} ${c}`
      | None => className
      },
      ref,
    })
  })
}
```

### Usage

```rescript
let Button = CSS.styled("button", `
  background-color: #2563eb;
  padding: 10px 20px;
  border-radius: 6px;
  color: white;
  font-weight: 600;

  &:hover {
    background-color: #1d4ed8;
  }

  &:disabled {
    opacity: 0.5;
    cursor: not-allowed;
  }
`)

// Typo = compile error:
let Bad = CSS.styled("div", `
  backgrond-color: red;
  // ^^^^^^^ Error: Unknown CSS property "backgrond-color". Did you mean "background-color"?
`)

// Usage in JSX — it's just a React component
<Button onClick={handleClick} disabled={isLoading}>
  {React.string("Submit")}
</Button>
```

---

## 4. SQL (replaces `rescript-embed-lang` / type-safe SQL)

### Comptime library

```rescript
// === SQL.res ===

@comptime
let sql = (comptime query: string, comptime schema: DBSchema.t) => {
  let parsed = Parser.parse(query)

  // Validate table/column names against schema
  Validator.validate(parsed, schema)
  // @compileError(`Column "naem" not found in table "users". Did you mean "name"?`)

  // Extract $param types from schema
  let params = extractParams(parsed, schema)

  // Infer result row type from SELECT columns
  let columns = inferColumns(parsed, schema)

  {
    query: query,
    execute: async (db: DB.t, params: @buildRecord(params)): array<@buildRecord(columns)> => {
      await db.query(query, params)
    },
    executeOne: async (db: DB.t, params: @buildRecord(params)): option<@buildRecord(columns)> => {
      let rows = await db.query(query, params)
      rows->Array.get(0)
    },
  }
}
```

### Usage

```rescript
@comptime let schema = DBSchema.load(@embedFile("./schema.sql"))

let findUser = SQL.sql(`SELECT id, name, email FROM users WHERE id = $id`, schema)
let searchUsers = SQL.sql(`SELECT id, name FROM users WHERE name LIKE $pattern LIMIT $limit`, schema)

// Fully typed params and results:
let user = await findUser.executeOne(db, {id: "123"})
// user: option<{id: string, name: string, email: string}>

let users = await searchUsers.execute(db, {pattern: "%alice%", limit: 10})
// users: array<{id: string, name: string}>

// Wrong column name = compile error:
let bad = SQL.sql(`SELECT nmae FROM users`, schema)
// Error: Column "nmae" not found in table "users". Did you mean "name"?
```

---

## 5. Form Generation (replaces `ppx_react_hook_form`)

### Comptime library

```rescript
// === Form.res ===

@comptime.derive("form")
let form = (comptime T: type) => {
  switch @typeInfo(T) {
  | Record({fields}) => {
      useForm: (): form<T> => {
        let rhf = ReactHookForm.useForm()
        {
          handleSubmit: rhf.handleSubmit,
          formState: rhf.formState,
          register: inline for field in fields {
            @record(field.name, rhf.register(field.name))
          },
          watch: inline for field in fields {
            @record(field.name, () => rhf.watch(field.name))
          },
        }
      }
    }
  | _ => @compileError("@form requires a record type")
  }
}
```

### Usage

```rescript
@form
type loginForm = {
  email: string,
  password: string,
  @form.min(1) @form.max(100) age: int,
  rememberMe: bool,
}

@react.component
let make = () => {
  let form = LoginForm.useForm()

  <form onSubmit={form.handleSubmit(data => Console.log(data))}>
    <input {...form.register.email} />
    <input {...form.register.password} type_="password" />
    <input {...form.register.age} type_="number" />
    <label>
      <input {...form.register.rememberMe} type_="checkbox" />
      {React.string("Remember me")}
    </label>
    <button type_="submit"> {React.string("Login")} </button>
  </form>
}
```

---

## 6. Type Building (replaces `ppx_ts` utility types)

Comptime value functions (`@comptime let`) take values and return values. Comptime type functions (`@comptime type`) take types and return types. Both use `@typeInfo` for introspection, but type functions use type-building builtins (`@buildVariant`, `@buildRecord`) to construct new type declarations.

### KeyOf — variant of record field names

```rescript
// === TypeUtils.res ===

// Type-level comptime: takes a type, returns a type
@comptime
type keyOf<'T> = {
  switch @typeInfo('T) {
  | Record({fields}) =>
    @buildVariant(inline for field in fields {
      @variantCase({name: field.name->String.capitalize, as: field.name})
    })
  | _ => @compileError("keyOf requires a record type")
  }
}
```

```rescript
// === Usage — just a type expression, no attributes needed ===

type user = { name: string, age: int, email: string }

type user_key = keyOf<user>
// Compiler evaluates at compile time, produces:
// type user_key =
//   | @as("name") Name
//   | @as("age") Age
//   | @as("email") Email

// Use it:
let fieldName = (key: user_key): string => {
  switch key {
  | Name => "name"
  | Age => "age"
  | Email => "email"
  }
}
```

### Partial — make all fields optional

```rescript
@comptime
type partial<'T> = {
  switch @typeInfo('T) {
  | Record({fields}) =>
    @buildRecord(inline for field in fields {
      @recordField({name: field.name, typ: field.typ, optional: true})
    })
  | _ => @compileError("partial requires a record type")
  }
}
```

```rescript
type user = { name: string, age: int, email: string }

type userPatch = partial<user>
// Produces:
// type userPatch = { name?: string, age?: int, email?: string }

let patch: userPatch = { name: "Alice" }  // age and email omitted
```

### Pick — subset of record fields

```rescript
@comptime
type pick<'T, 'Keys> = {
  switch @typeInfo('T) {
  | Record({fields}) =>
    let keys = @comptimeValue('Keys)  // extract the comptime string array
    let picked = fields->Array.filter(f => Array.includes(keys, f.name))
    if Array.length(picked) != Array.length(keys) {
      let unknown = keys->Array.filter(k => !Array.some(fields, f => f.name == k))
      @compileError(`Unknown fields: ${Array.join(unknown, ", ")}`)
    }
    @buildRecord(inline for field in picked {
      @recordField({name: field.name, typ: field.typ})
    })
  | _ => @compileError("pick requires a record type")
  }
}
```

```rescript
type user = { name: string, age: int, email: string }

type userPreview = pick<user, ["name", "email"]>
// Produces:
// type userPreview = { name: string, email: string }

// Typo in field name = compile error:
type bad = pick<user, ["name", "emial"]>
// Error: Unknown fields: emial
```

### Readonly — make all fields immutable (strip mutable)

```rescript
@comptime
type readonly<'T> = {
  switch @typeInfo('T) {
  | Record({fields}) =>
    @buildRecord(inline for field in fields {
      @recordField({name: field.name, typ: field.typ, mutable_: false})
    })
  | _ => @compileError("readonly requires a record type")
  }
}
```

```rescript
type state = { mutable count: int, mutable label: string }

type frozenState = readonly<state>
// Produces:
// type frozenState = { count: int, label: string }
```

### Enum from string array

```rescript
@comptime
type makeEnum<'Values> = {
  let values = @comptimeValue('Values)
  @buildVariant(inline for v in values {
    @variantCase({name: v->String.capitalize, as: v})
  })
}
```

```rescript
type status = makeEnum<["active", "inactive", "suspended"]>
// Produces:
// type status =
//   | @as("active") Active
//   | @as("inactive") Inactive
//   | @as("suspended") Suspended
```

### Composing type-level comptime

Comptime types compose naturally — the output of one can be the input to another:

```rescript
type user = { name: string, age: int, email: string, password: string }

// Pick some fields, then make them optional
type userPatch = partial<pick<user, ["name", "age", "email"]>>
// Produces:
// type userPatch = { name?: string, age?: int, email?: string }

// Keys of a subset
type editableFields = keyOf<pick<user, ["name", "age", "email"]>>
// Produces:
// type editableFields = | @as("name") Name | @as("age") Age | @as("email") Email
```

### Derive attributes still work for type-level comptime

If you want attribute-triggered type generation (like `@keyOf` on a type declaration), `@comptime.derive` works with comptime types too:

```rescript
// Register keyOf as a derive attribute
@comptime.derive("keyOf")
type keyOf<'T> = { ... }  // same body as above

// Now both styles work:
type user_key = keyOf<user>           // explicit call
@keyOf type user = { ... }            // derive attribute — generates user_key alongside
```

---

## Summary

Comptime has two modes, matching the two things you do in a language — compute values and define types:

| | Value-level comptime | Type-level comptime |
|---|---|---|
| **Syntax** | `@comptime let f = ...` | `@comptime type f<'T> = ...` |
| **Input** | Types + runtime values | Types only |
| **Output** | Specialized runtime code | New type declarations |
| **Usage** | `f(myType, myValue)` | `type t = f<myType>` |
| **Example** | JSON encoder | keyOf, partial, pick |

Both use the same introspection (`@typeInfo`, `@getAttr`, `inline for`) and the same execution model (QuickJS). The difference is just what they produce — runtime expressions vs type declarations.

Key primitives:
- `@typeInfo(T)` — structured type introspection
- `inline for` — compile-time loop unrolling
- `@compileError(msg)` — user-friendly error messages
- `@field(value, name)` — comptime-known field access
- `@getAttr(field, name)` — read custom attributes
- `@embedFile(path)` — embed file contents at compile time
- `@buildVariant` / `@variantCase` — construct variant types
- `@buildRecord` / `@recordField` — construct record types
