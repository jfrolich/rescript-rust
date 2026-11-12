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
   and for a type the compiler's handle of it. `m` says which parts of the
   text are text from elsewhere, an argument of the macro or a quote: the
   compiler reports an error in generated code with it. `o`: the type
   inside, for an option type a macro built with `Type.option`. */
type span
type rec node = {c: string, m?: array<span>, id?: int, t?: node, raw?: bool, o?: node}

external toNode: 'a => node = "%identity"
external ofNode: node => 'a = "%identity"

let make = (source: string): 'a => ofNode({c: source})
let source = (value: 'a): string => toNode(value).c

/* One node of several, in order. A span is `[start, length, ...origin]`. */
let cat: array<node> => node = %raw(`function (parts) {
  var c = "", m;
  for (var i = 0; i < parts.length; i++) {
    var part = parts[i];
    if (part.m !== undefined) {
      if (m === undefined) m = [];
      for (var j = 0; j < part.m.length; j++) {
        var span = part.m[j].slice();
        span[0] += c.length;
        m.push(span);
      }
    }
    c += part.c;
  }
  return m === undefined ? {c: c} : {c: c, m: m};
}`)

let text = (source: string): node => {c: source}
let build = (parts: array<node>): 'a => ofNode(cat(parts))

/* The nodes with `separator` between them. */
let join = (nodes: array<node>, separator: string): node => {
  let parts = []
  nodes->Array.forEachWithIndex((node, index) => {
    if index > 0 {
      parts->Array.push(text(separator))
    }
    parts->Array.push(node)
  })
  cat(parts)
}

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
let __holeItem = (value: code<'a>): hole => ofNode({...toNode(value), raw: true})
/* The body of a type declaration, `type t = ${body}`: a record or a variant
   type cannot be written in parentheses. */
let __holeTypeBody = (value: typ): hole => ofNode({...toNode(value), raw: true})

/* A piece is the text between two holes: parts of the macro's file, each
   with its line and column there (line 0: text that is not from the file). */
type piece = array<(string, int, int)>

let quote: (array<piece>, array<hole>, string) => node = %raw(`function (pieces, holes, file) {
  var parts = [];
  function add(piece) {
    for (var i = 0; i < piece.length; i++) {
      var fragment = piece[i];
      parts.push(
        fragment[1] > 0
          ? {c: fragment[0], m: [[0, fragment[0].length, file, fragment[1], fragment[2]]]}
          : {c: fragment[0]}
      );
    }
  }
  add(pieces[0]);
  for (var i = 0; i < holes.length; i++) {
    var hole = holes[i];
    if (hole.raw === true) {
      parts.push(hole);
    } else {
      parts.push({c: "("}, hole, {c: ")"});
    }
    add(pieces[i + 1]);
  }
  return cat(parts);
}`)

let __quoteCode = (pieces, holes, file): code<'a> => ofNode(quote(pieces, holes, file))
let __quoteDecls = (pieces, holes, file): decls => ofNode(quote(pieces, holes, file))
let __quoteType = (pieces, holes, file): typ => ofNode(quote(pieces, holes, file))
let __quotePat = (pieces, holes, file): pat => ofNode(quote(pieces, holes, file))

/* Splice holes. `${...items}` in a list of a quote stands for any number
   of its items; the compiler picks the function by the list. `trailing`:
   a comma follows the hole. That comma is the hole's own, so that a hole
   with no items leaves no comma behind. */
let splice = (items: array<node>, trailing: bool): hole =>
  ofNode({...cat([join(items, ", "), text(trailing && items->Array.length > 0 ? "," : "")]), raw: true})

/** A field of a record value: see `Code.entry`. */
type recordEntry

/* The spread of a record comes before its fields. */
let entryNodes = (entries: array<recordEntry>): array<node> => {
  let nodes = entries->Array.map(toNode)
  let isSpread = (node: node) => node.c->String.startsWith("...")
  let spreads = nodes->Array.filter(isSpread)
  if spreads->Array.length > 1 {
    host->fail(
      "A record can have one spread, and these fields have more: " ++ spreads->Array.map(node => node.c)->Array.join(", "),
      None,
    )
  } else {
    spreads->Array.concat(nodes->Array.filter(node => !isSpread(node)))
  }
}

let caseNode = ((pattern, body): (pat, code<'a>)): node =>
  cat([text("| "), toNode(pattern), text(" => "), toNode(body)])

let __spliceItems = (items: array<code<'a>>, trailing: bool): hole => splice(items->Array.map(toNode), trailing)
let __spliceEntries = (entries: array<recordEntry>, trailing: bool): hole => splice(entryNodes(entries), trailing)
let __spliceCases = (cases: array<(pat, code<'a>)>): hole =>
  ofNode({...join(cases->Array.map(caseNode), "\n"), raw: true})

let isSimple: string => bool = %raw(`function (text) {
  return /^[A-Za-z_][A-Za-z0-9_$.]*$/.test(text)
}`)
let atom = (text: string) => isSimple(text) ? text : "(" ++ text ++ ")"
/* `node` where an operand is expected: in parentheses unless it is a name. */
let atomNode = (node: node): node => isSimple(node.c) ? node : cat([text("("), node, text(")")])

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
    /**
    The type of `value.name`. For an optional field `age?: int` that is
    `option<int>`: reading the field, `Code.entryOf` and `Pat.constructor`
    all use this type.
    */
    typ: typ,
    /** `age?: int`. Change it with `Type.optional` and `Type.required`. */
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

  /** `option<t>` */
  let option = (t: typ): typ => ofNode({c: "option<" ++ source(t) ++ ">", o: toNode(t)})

  /* The `t` of `option<t>`. */
  let optionOf = (t: typ): option<typ> => {
    let node = toNode(t)
    switch (node.o, node.id) {
    | (Some(inner), _) => Some(ofNode(inner))
    | (None, Some(_)) =>
      switch info(t) {
      | Option(inner) => Some(inner)
      | _ => None
      }
    | (None, None) => None
    }
  }

  /* The type an optional field is declared with: `int` for `age?: int`,
     where `typ` is `option<int>`. */
  let declared = (field: field): typ =>
    switch optionOf(field.typ) {
    | Some(inner) => inner
    | None =>
      error(
        "The optional field `" ++
        field.name ++
        "` has the type `" ++
        source(field.typ) ++ "`, and the type of an optional field is an option. Type.optional makes a field optional.",
      )
    }

  /**
  The field as an optional one: `age?: int`. Its `typ` becomes
  `option<int>`, the type of `value.age`. An optional field stays as it is.
  */
  let optional = (field: field): field =>
    field.optional ? field : {...field, optional: true, typ: option(field.typ)}

  /** The field as a required one: `age: int` for `age?: int`. */
  let required = (field: field): field =>
    field.optional ? {...field, optional: false, typ: declared(field)} : field

  let fieldText = (field: field): string =>
    attrText(field.attrs) ++
    (field.jsName != field.name ? "@as(" ++ JSON.stringify(JSON.Encode.string(field.jsName)) ++ ") " : "") ++
    (field.mutable_ ? "mutable " : "") ++
    field.name ++ (field.optional ? "?: " ++ source(declared(field)) : ": " ++ source(field.typ))

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
  let field = (value: code<'a>, name: string): code<'b> => build([atomNode(toNode(value)), text("." ++ name)])

  /** `[a, b, c]` */
  let array = (items: array<code<'a>>): code<array<'a>> =>
    build([text("["), join(items->Array.map(toNode), ", "), text("]")])

  /** `(a, b, c)` */
  let tuple = (items: array<code<'a>>): code<'b> =>
    build([text("("), join(items->Array.map(toNode), ", "), text(")")])

  /** The same code without its type, to put code of different types in one array. */
  external untyped: code<'a> => code<unknown> = "%identity"

  /** `@name value`, or `@name(payload) value`. */
  let withAttr = (value: code<'a>, name: string, ~payload: option<code<'b>>=?): code<'a> =>
    build([
      text("@" ++ name),
      switch payload {
      | Some(payload) => cat([text("("), toNode(payload), text(") ")])
      | None => text(" ")
      },
      atomNode(toNode(value)),
    ])

  /** A field of a record value: `name: value`, `name: ?value` or `...value`. */
  type entry = recordEntry

  /**
  `name: value`. With `~optional=true`, `name: ?value`: the value is an
  option, and `None` leaves the field out.
  */
  let entry = (name: string, value: code<'a>, ~optional=false): entry =>
    build([text(name ++ (optional ? ": ?" : ": ")), optional ? atomNode(toNode(value)) : toNode(value)])

  /**
  The entry of a field of a record type, for a value of the type `field.typ`:
  `name: ?value` when the field is optional, `name: value` otherwise.
  */
  let entryOf = (field: Type.field, value: code<'a>): entry => entry(field.name, value, ~optional=field.optional)

  /** `...value`: the fields of another record of the same type. */
  let spread = (value: code<'a>): entry => build([text("..."), atomNode(toNode(value))])

  /** `{name: value, ...}` */
  let record = (entries: array<entry>): code<'a> => build([text("{"), join(entryNodes(entries), ", "), text("}")])

  /** `f(a, b)` */
  let call = (f: code<'a>, args: array<code<'b>>): code<'c> =>
    build([atomNode(toNode(f)), text("("), join(args->Array.map(toNode), ", "), text(")")])

  /** `switch value { | pattern => body ... }` */
  let switch_ = (value: code<'a>, arms: array<(pat, code<'b>)>): code<'b> =>
    build([text("switch "), atomNode(toNode(value)), text(" {\n"), join(arms->Array.map(caseNode), "\n"), text("\n}")])

  /** A parameter of `fn`. */
  type param = string

  /** `name: typ` */
  let param = (name: string, typ: typ): param => name ++ ": " ++ source(typ)

  /** `~name: typ` */
  let labelled = (name: string, typ: typ): param => "~" ++ name ++ ": " ++ source(typ)

  /** `(params) => body` */
  let fn = (params: array<param>, body: code<'a>): code<'f> =>
    build([text("(" ++ params->Array.join(", ") ++ ") => "), toNode(body)])

  /** Several declarations, one after the other. */
  let decls = (items: array<decls>): decls => build([join(items->Array.map(toNode), "\n")])

  /** `module Name = { items }`, for a module whose name is computed. */
  let module_ = (name: string, items: decls): decls =>
    build([text("module " ++ name ++ " = {\n"), toNode(items), text("\n}")])
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
          c.fields
          // `?`: the name is bound to the option of an optional field, absent or not.
          ->Array.mapWithIndex((f, i) => f.name ++ (f.optional ? ": ?" : ": ") ++ names->Array.getUnsafe(i))
          ->Array.join(", ") ++ "})",
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
