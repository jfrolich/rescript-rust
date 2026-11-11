/***
Compile-time macros.

A macro is a ReScript function the compiler runs while it compiles another
file. It returns code, written as a quote: `%code(...)` for an expression or
declarations, `%type(...)` for a type and `%pat(...)` for a pattern. Inside a
quote, `${...}` is a hole that takes a value of type `code`, `typ` or `pat`.

See `docs/comptime/README.md` for the design.
*/

open Stdlib

/** A piece of ReScript code that evaluates to a value of type `'a`. */
type code<'a>

/** A type. */
type typ

/** A pattern. */
type pat

type declarations

/** Declarations: the result of a macro that adds `let`s, types or modules. */
type decls = code<declarations>

/* The representation the compiler and the engine share: the source text,
   and for a type the compiler's handle of it. */
type rec node = {c: string, id?: int, t?: node, raw?: bool}

external toNode: 'a => node = "%identity"
external ofNode: node => 'a = "%identity"

let make = (source: string): 'a => ofNode({c: source})
let source = (value: 'a): string => toNode(value).c

type host
@val external host: host = "__rescript_macro"
@send external ask: (host, string) => 'a = "ask"
@send external fail: (host, string, option<int>) => 'a = "fail"
@send external expectedType: host => Nullable.t<typ> = "expected"

/** Stop compilation with `message`, reported at the macro call. */
let error = (message: string): 'a => host->fail(message, None)

/** Like `error`, for a mistake at `offset` characters into a string argument. */
let errorAt = (~offset: int, message: string): 'a => host->fail(message, Some(offset))

/** The type of an argument of a `@generic` macro. */
let typeOf = (value: code<'a>): typ =>
  switch toNode(value).t {
  | Some(t) => ofNode(t)
  | None => error("typeOf: the type of this code is not known. Only the arguments of a macro carry a type.")
  }

/** The type the call site of a `@generic` macro expects as result. */
let expected = (): typ =>
  switch host->expectedType->Nullable.toOption {
  | Some(t) => t
  | None => error("expected: only a @generic macro knows the type its call site expects.")
  }

/** The text of a file. The build tracks it as an input of the macro. */
let readFile = (path: string): string => host->ask("readFile:" ++ path)

/** An environment variable of the build. */
let env = (name: string): option<string> => Nullable.toOption(host->ask("env:" ++ name))

/* Quotes. The compiler rewrites `%code(a + ${b})` to a call of `__quoteCode`
   with the text around the holes and the hole values. */
type hole

external __holeCode: code<'a> => hole = "%identity"
external __holeType: typ => hole = "%identity"
external __holePat: pat => hole = "%identity"
let __holeItem = (value: code<'a>): hole => ofNode({c: source(value), raw: true})

let quote = (pieces: array<string>, holes: array<hole>): node => {
  let text = ref(pieces->Array.getUnsafe(0))
  holes->Array.forEachWithIndex((hole, index) => {
    let hole = toNode(hole)
    let filled = hole.raw == Some(true) ? hole.c : "(" ++ hole.c ++ ")"
    text := text.contents ++ filled ++ pieces->Array.getUnsafe(index + 1)
  })
  {c: text.contents}
}

let __quoteCode = (pieces, holes): code<'a> => ofNode(quote(pieces, holes))
let __quoteDecls = (pieces, holes): decls => ofNode(quote(pieces, holes))
let __quoteType = (pieces, holes): typ => ofNode(quote(pieces, holes))
let __quotePat = (pieces, holes): pat => ofNode(quote(pieces, holes))

let isSimple: string => bool = %raw(`function (text) {
  return /^[A-Za-z_][A-Za-z0-9_$.]*$/.test(text)
}`)
let atom = (text: string) => isSimple(text) ? text : "(" ++ text ++ ")"

module Attr = {
  /** An attribute: `@Json.key("user_age")` has the name `Json.key` and the payload `user_age`. */
  type t = {
    name: string,
    /** The payload, when it is one string literal. */
    payload: option<string>,
  }

  let find = (attrs: array<t>, name: string): option<t> => attrs->Array.find(attr => attr.name == name)
  let has = (attrs: array<t>, name: string): bool => find(attrs, name) != None
  let string = (attrs: array<t>, name: string): option<string> =>
    switch find(attrs, name) {
    | Some({payload}) => payload
    | None => None
    }
}

module Type = {
  // `open Macro` puts this module in the place of the standard library's
  // `Type`, so it has everything that one has.
  include Stdlib_Type

  type field = {
    name: string,
    /** The name at run time: the `@as` name when there is one. */
    jsName: string,
    typ: typ,
    optional: bool,
    mutable_: bool,
    attrs: array<Attr.t>,
  }

  type constructor = {
    name: string,
    /** The value or tag at run time: the `@as` value when there is one. */
    jsName: string,
    args: array<typ>,
    /** The fields of an inline record argument, `Circle({radius: float})`. */
    fields: array<field>,
    attrs: array<Attr.t>,
  }

  /** What the type checker knows about a type, one level deep. */
  type info =
    | Int
    | Float
    | String
    | Bool
    | Unit
    | BigInt
    | Char
    | Option(typ)
    | Array(typ)
    | List(typ)
    | Dict(typ)
    | Promise(typ)
    | Result(typ, typ)
    | Tuple(array<typ>)
    | Record({name: string, fields: array<field>, attrs: array<Attr.t>})
    | Variant({name: string, constructors: array<constructor>, attrs: array<Attr.t>})
    | PolyVariant({constructors: array<constructor>})
    | Function({params: array<typ>, result: typ})
    /** A type whose definition is hidden by an interface, or an external type. */
    | Abstract({name: string})
    /** A type that inference has not settled. */
    | Unknown

  /** A type declaration, as a macro on a type receives it. */
  type decl = {
    name: string,
    typ: typ,
    attrs: array<Attr.t>,
  }

  let handle = (t: typ, what: string): int =>
    switch toNode(t).id {
    | Some(id) => id
    | None => error(what ++ ": this type was built by a macro, so the compiler has no information on it.")
    }

  let info = (t: typ): info => host->ask("info:" ++ Int.toString(handle(t, "Type.info")))

  /** The type as source text, such as `array<string>`. */
  let name = (t: typ): string => source(t)

  /** The value `name` of the module that defines the type: `Date.toJson` for `Date.t`. */
  let companion = (t: typ, name: string): option<code<'a>> =>
    Nullable.toOption(host->ask("companion:" ++ Int.toString(handle(t, "Type.companion")) ++ ":" ++ name))

  let attrText = (attrs: array<Attr.t>): string =>
    attrs
    ->Array.map(attr =>
      switch attr.payload {
      | Some(payload) => "@" ++ attr.name ++ "(" ++ JSON.stringify(JSON.Encode.string(payload)) ++ ") "
      | None => "@" ++ attr.name ++ " "
      }
    )
    ->Array.join("")

  let fieldText = (field: field): string =>
    attrText(field.attrs) ++
    (field.jsName != field.name ? "@as(" ++ JSON.stringify(JSON.Encode.string(field.jsName)) ++ ") " : "") ++
    (field.mutable_ ? "mutable " : "") ++
    field.name ++
    (field.optional ? "?: " : ": ") ++
    source(field.typ)

  /** A record type with these fields. */
  let record = (fields: array<field>): typ => make("{" ++ fields->Array.map(fieldText)->Array.join(", ") ++ "}")

  /** A variant type with these constructors. Use it as the body of a type declaration. */
  let variant = (constructors: array<constructor>): typ =>
    make(
      constructors
      ->Array.map(c =>
        "| " ++
        attrText(c.attrs) ++
        (c.jsName != c.name ? "@as(" ++ JSON.stringify(JSON.Encode.string(c.jsName)) ++ ") " : "") ++
        c.name ++ (
          c.fields->Array.length > 0
            ? "({" ++ c.fields->Array.map(fieldText)->Array.join(", ") ++ "})"
            : c.args->Array.length > 0
            ? "(" ++ c.args->Array.map(source)->Array.join(", ") ++ ")"
            : ""
        )
      )
      ->Array.join(" "),
    )

  /** A field for `record`. */
  let field = (name: string, typ: typ): field => {
    name,
    jsName: name,
    typ,
    optional: false,
    mutable_: false,
    attrs: [],
  }

  /** A constructor without arguments for `variant`. */
  let constructor = (name: string): constructor => {
    name,
    jsName: name,
    args: [],
    fields: [],
    attrs: [],
  }
}

module Code = {
  /** A string literal. */
  let string = (value: string): code<string> => make(JSON.stringify(JSON.Encode.string(value)))
  let int = (value: int): code<int> => make(Int.toString(value))
  let float = (value: float): code<float> => {
    let text = Float.toString(value)
    make(text->String.includes(".") || text->String.includes("e") ? text : text ++ ".")
  }
  let bool = (value: bool): code<bool> => make(value ? "true" : "false")
  let unit: code<unit> = make("()")

  /** The source text of a piece of code. */
  let print = (value: code<'a>): string => source(value)

  /** Code from source text. Nothing checks it until the macro's result is compiled. */
  let raw = (text: string): code<'a> => make(text)

  /** A name that is resolved where the macro is used, not where it is defined. */
  let ident = (name: string): code<'a> => make(name)

  /** `value.name` */
  let field = (value: code<'a>, name: string): code<'b> => make(atom(source(value)) ++ "." ++ name)

  /** `[a, b, c]` */
  let array = (items: array<code<'a>>): code<array<'a>> =>
    make("[" ++ items->Array.map(source)->Array.join(", ") ++ "]")

  /** `(a, b, c)` */
  let tuple = (items: array<code<'a>>): code<'b> => make("(" ++ items->Array.map(source)->Array.join(", ") ++ ")")

  /** `{name: value, ...}` */
  let record = (fields: array<(string, code<'a>)>): code<'b> =>
    make("{" ++ fields->Array.map(((name, value)) => name ++ ": " ++ source(value))->Array.join(", ") ++ "}")

  /** `f(a, b)` */
  let call = (f: code<'a>, args: array<code<'b>>): code<'c> =>
    make(atom(source(f)) ++ "(" ++ args->Array.map(source)->Array.join(", ") ++ ")")

  /** `switch value { | pattern => body ... }` */
  let switch_ = (value: code<'a>, arms: array<(pat, code<'b>)>): code<'b> =>
    make(
      "switch " ++
      atom(source(value)) ++
      " {\n" ++
      arms->Array.map(((pattern, body)) => "| " ++ source(pattern) ++ " => " ++ source(body))->Array.join("\n") ++ "\n}",
    )

  /** A parameter of `fn`. */
  type param = string

  /** `name: typ` */
  let param = (name: string, typ: typ): param => name ++ ": " ++ source(typ)

  /** `~name: typ` */
  let labelled = (name: string, typ: typ): param => "~" ++ name ++ ": " ++ source(typ)

  /** `(params) => body` */
  let fn = (params: array<param>, body: code<'a>): code<'f> =>
    make("(" ++ params->Array.join(", ") ++ ") => " ++ source(body))

  /** Several declarations, one after the other. */
  let decls = (items: array<decls>): decls => make(items->Array.map(source)->Array.join("\n"))
}

module Pat = {
  /** A variable pattern. */
  let var = (name: string): pat => make(name)

  /** `_` */
  let any: pat = make("_")

  /** A string literal pattern. */
  let string = (value: string): pat => make(JSON.stringify(JSON.Encode.string(value)))

  /** An integer literal pattern. */
  let int = (value: int): pat => make(Int.toString(value))

  /**
  The pattern that matches a constructor and binds its arguments, with the
  code of each bound argument: `Circle(a0, a1)` and `[a0, a1]`.
  */
  let constructor = (c: Type.constructor): (pat, array<code<'a>>) => {
    let typed = (name: string, typ: typ): code<'a> => ofNode({c: name, t: toNode(typ)})
    if c.fields->Array.length > 0 {
      let names = c.fields->Array.mapWithIndex((f, i) => f.name ++ "$" ++ Int.toString(i))
      (
        make(
          c.name ++
          "({" ++
          c.fields->Array.mapWithIndex((f, i) => f.name ++ ": " ++ names->Array.getUnsafe(i))->Array.join(", ") ++ "})",
        ),
        c.fields->Array.mapWithIndex((f, i) => typed(names->Array.getUnsafe(i), f.typ)),
      )
    } else if c.args->Array.length > 0 {
      let names = c.args->Array.mapWithIndex((_, i) => "arg$" ++ Int.toString(i))
      (make(c.name ++ "(" ++ names->Array.join(", ") ++ ")"), c.args->Array.mapWithIndex((typ, i) => typed(names->Array.getUnsafe(i), typ)))
    } else {
      (make(c.name), [])
    }
  }
}

module Decl = {
  /** A `let` binding, as a macro on a `let` receives it: before it is type checked. */
  type value = {
    /** The bound name, or `""` when the binding is a pattern. */
    name: string,
    pat: pat,
    expr: code<unknown>,
  }
}
