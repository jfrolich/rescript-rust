# Comptime Examples: Replacing PPXs

Concrete examples showing how comptime replaces every major PPX use case. Each section shows the current PPX pain, the full comptime implementation, and what the compiler produces.

---

## 1. JSON Codec (replaces `ppx_spice` / `Decco`)

### Comptime library

```rescript
// === Codec.res — reusable library, written in ReScript, not OCaml ===

@comptime
let rec encodeField = (comptime T: type, value: T): Js.Json.t => {
  switch @typeInfo(T) {
  | String => Js.Json.string(value)
  | Int => Js.Json.number(Int.toFloat(value))
  | Float => Js.Json.number(value)
  | Bool => Js.Json.boolean(value)
  | Option({inner}) =>
    switch value {
    | Some(v) => encodeField(inner, v)
    | None => Js.Json.null
    }
  | Array({element}) =>
    value->Array.map(v => encodeField(element, v))->Js.Json.array
  | Record({fields}) =>
    let obj = Js.Dict.empty()
    inline for field in fields {
      let key = @getAttr(field, "json.key")->Option.getOr(field.jsName)
      if field.optional {
        switch @field(value, field.name) {
        | Some(v) => Js.Dict.set(obj, key, encodeField(field.typ, v))
        | None => ()
        }
      } else {
        Js.Dict.set(obj, key, encodeField(field.typ, @field(value, field.name)))
      }
    }
    Js.Json.object_(obj)
  | Variant({constructors, tag}) =>
    let tagKey = tag->Option.getOr("TAG")
    inline for ctor in constructors {
      switch value {
      | @variant(ctor.name) =>
        let obj = Js.Dict.empty()
        Js.Dict.set(obj, tagKey, Js.Json.string(ctor.name))
        switch ctor.args {
        | NoArgs => ()
        | InlineRecord(fields) =>
          inline for f in fields {
            Js.Dict.set(obj, f.name, encodeField(f.typ, @ctorField(value, ctor.name, f.name)))
          }
        | TupleArgs(args) =>
          inline for (i, arg) in Array.withIndex(args) {
            Js.Dict.set(obj, `_${Int.toString(i)}`, encodeField(arg, @ctorArg(value, ctor.name, i)))
          }
        }
        Js.Json.object_(obj)
      }
    }
  | Recursive(_) => @callEncoder(T, value)
  | _ => @compileError(`Cannot encode ${@typeName(T)}`)
  }
}

@comptime.derive("encoder")
let encoder = (comptime T: type) => {
  (value: T): Js.Json.t => encodeField(T, value)
}

@comptime.derive("decoder")
let decoder = (comptime T: type) => {
  (json: Js.Json.t): result<T, string> => decodeField(T, json, "$")
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
let rec encode_treeNode = (value: treeNode): Js.Json.t => {
  let obj = Js.Dict.empty()
  Js.Dict.set(obj, "value", Js.Json.string(value.value))
  Js.Dict.set(obj, "children",
    value.children->Array.map(v => encode_treeNode(v))->Js.Json.array
  )
  Js.Json.object_(obj)
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
let encode_shape = (value: shape): Js.Json.t => {
  switch value {
  | Circle({radius}) =>
    let obj = Js.Dict.empty()
    Js.Dict.set(obj, "TAG", Js.Json.string("Circle"))
    Js.Dict.set(obj, "radius", Js.Json.number(radius))
    Js.Json.object_(obj)
  | Rectangle({width, height}) =>
    let obj = Js.Dict.empty()
    Js.Dict.set(obj, "TAG", Js.Json.string("Rectangle"))
    Js.Dict.set(obj, "width", Js.Json.number(width))
    Js.Dict.set(obj, "height", Js.Json.number(height))
    Js.Json.object_(obj)
  | Point =>
    let obj = Js.Dict.empty()
    Js.Dict.set(obj, "TAG", Js.Json.string("Point"))
    Js.Json.object_(obj)
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
    parseResponse: (json: Js.Json.t) => {
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

## 6. KeyOf / Utility Types (replaces `ppx_ts`)

### Comptime library

```rescript
// === TypeUtils.res ===

@comptime.derive("keyOf")
let keyOf = (comptime T: type) => {
  switch @typeInfo(T) {
  | Record({fields}) =>
    @buildVariant(inline for field in fields {
      @variantCase(String.capitalize(field.name), @as(field.name))
    })
  | _ => @compileError("@keyOf requires a record type")
  }
}

@comptime.derive("pick")
let pick = (comptime T: type, comptime keys: array<string>) => {
  switch @typeInfo(T) {
  | Record({fields}) =>
    let picked = fields->Array.filter(f => Array.includes(keys, f.name))
    if Array.length(picked) != Array.length(keys) {
      let unknown = keys->Array.filter(k => !Array.some(fields, f => f.name == k))
      @compileError(`Unknown fields: ${Array.join(unknown, ", ")}`)
    }
    @buildRecord(picked)
  | _ => @compileError("@pick requires a record type")
  }
}

@comptime.derive("partial")
let partial = (comptime T: type) => {
  switch @typeInfo(T) {
  | Record({fields}) =>
    @buildRecord(fields->Array.map(f => {...f, optional: true}))
  | _ => @compileError("@partial requires a record type")
  }
}
```

### Usage

```rescript
@keyOf @partial
type user = {
  name: string,
  age: int,
  email: string,
}

// Generated:
// type user_key = Name | Age | Email  (each @as("name") etc.)
// type user_partial = { name?: string, age?: int, email?: string }

type userPreview = TypeUtils.pick<user, ["name", "email"]>
// = { name: string, email: string }
```

---

## Summary

The common pattern across all examples:

1. **PPX today**: Write OCaml code that manipulates raw AST nodes. Requires separate toolchain, hard to debug, breaks on AST changes.
2. **Comptime**: Write ReScript code that works with structured `typeInfo` data. Runs in QuickJS during compilation. Produces specialized code with zero runtime overhead.

Key primitives that make it work:
- `@typeInfo(T)` — structured type introspection
- `inline for` — compile-time loop unrolling
- `@compileError(msg)` — user-friendly error messages
- `@field(value, name)` — comptime-known field access
- `@getAttr(field, name)` — read custom attributes
- `@embedFile(path)` — embed file contents at compile time
