

import * as Stdlib_Type from "./Stdlib_Type.mjs";
import * as Primitive_object from "./Primitive_object.mjs";
import * as Primitive_option from "./Primitive_option.mjs";

function make(source) {
  return {
    c: source
  };
}

function source(value) {
  return value.c;
}

function error(message) {
  return __rescript_macro.fail(message, undefined);
}

function errorAt(offset, message) {
  return __rescript_macro.fail(message, offset);
}

function typeOf(value) {
  let t = value.t;
  if (t !== undefined) {
    return t;
  } else {
    return __rescript_macro.fail("typeOf: the type of this code is not known. Only the arguments of a macro carry a type.", undefined);
  }
}

function expected() {
  let t = __rescript_macro.expected();
  if (t == null) {
    return __rescript_macro.fail("expected: only a @generic macro knows the type its call site expects.", undefined);
  } else {
    return t;
  }
}

function readFile(path) {
  return __rescript_macro.ask("readFile:" + path);
}

function env(name) {
  return Primitive_option.fromNullable(__rescript_macro.ask("env:" + name));
}

function __holeItem(value) {
  return {
    c: value.c,
    raw: true
  };
}

function quote(pieces, holes) {
  let text = pieces[0];
  holes.forEach((hole, index) => {
    let filled = Primitive_object.equal(hole.raw, true) ? hole.c : "(" + hole.c + ")";
    text = text + filled + pieces[index + 1 | 0];
  });
  return {
    c: text
  };
}

let __quoteCode = quote;

let __quoteDecls = quote;

let __quoteType = quote;

let __quotePat = quote;

let isSimple = (function (text) {
  return /^[A-Za-z_][A-Za-z0-9_$.]*$/.test(text)
});

function atom(text) {
  if (isSimple(text)) {
    return text;
  } else {
    return "(" + text + ")";
  }
}

function find(attrs, name) {
  return attrs.find(attr => attr.name === name);
}

function has(attrs, name) {
  return find(attrs, name) !== undefined;
}

function string(attrs, name) {
  let match = find(attrs, name);
  if (match !== undefined) {
    return match.payload;
  }
}

let Attr = {
  find: find,
  has: has,
  string: string
};

function handle(t, what) {
  let id = t.id;
  if (id !== undefined) {
    return id;
  } else {
    return __rescript_macro.fail(what + ": this type was built by a macro, so the compiler has no information on it.", undefined);
  }
}

function info(t) {
  return __rescript_macro.ask("info:" + handle(t, "Type.info").toString());
}

function name(t) {
  return t.c;
}

function companion(t, name) {
  return Primitive_option.fromNullable(__rescript_macro.ask("companion:" + handle(t, "Type.companion").toString() + ":" + name));
}

function attrText(attrs) {
  return attrs.map(attr => {
    let payload = attr.payload;
    if (payload !== undefined) {
      return "@" + attr.name + "(" + JSON.stringify(payload) + ") ";
    } else {
      return "@" + attr.name + " ";
    }
  }).join("");
}

function fieldText(field) {
  return attrText(field.attrs) + (
    field.jsName !== field.name ? "@as(" + JSON.stringify(field.jsName) + ") " : ""
  ) + (
    field.mutable_ ? "mutable " : ""
  ) + field.name + (
    field.optional ? "?: " : ": "
  ) + field.typ.c;
}

function record(fields) {
  return make("{" + fields.map(fieldText).join(", ") + "}");
}

function variant(constructors) {
  return make(constructors.map(c => "| " + attrText(c.attrs) + (
    c.jsName !== c.name ? "@as(" + JSON.stringify(c.jsName) + ") " : ""
  ) + c.name + (
    c.fields.length !== 0 ? "({" + c.fields.map(fieldText).join(", ") + "})" : (
        c.args.length !== 0 ? "(" + c.args.map(source).join(", ") + ")" : ""
      )
  )).join(" "));
}

function field(name, typ) {
  return {
    name: name,
    jsName: name,
    typ: typ,
    optional: false,
    mutable_: false,
    attrs: []
  };
}

function constructor(name) {
  return {
    name: name,
    jsName: name,
    args: [],
    fields: [],
    attrs: []
  };
}

let Type = {
  Classify: Stdlib_Type.Classify,
  handle: handle,
  info: info,
  name: name,
  companion: companion,
  attrText: attrText,
  fieldText: fieldText,
  record: record,
  variant: variant,
  field: field,
  constructor: constructor
};

function string$1(value) {
  return make(JSON.stringify(value));
}

function int(value) {
  return make(value.toString());
}

function float(value) {
  let text = value.toString();
  return make(text.includes(".") || text.includes("e") ? text : text + ".");
}

function bool(value) {
  return make(value ? "true" : "false");
}

let unit = {
  c: "()"
};

function print(value) {
  return value.c;
}

let raw = make;

let ident = make;

function field$1(value, name) {
  return make(atom(value.c) + "." + name);
}

function array(items) {
  return make("[" + items.map(source).join(", ") + "]");
}

function tuple(items) {
  return make("(" + items.map(source).join(", ") + ")");
}

function record$1(fields) {
  return make("{" + fields.map(param => param[0] + ": " + param[1].c).join(", ") + "}");
}

function call(f, args) {
  return make(atom(f.c) + "(" + args.map(source).join(", ") + ")");
}

function switch_(value, arms) {
  return make("switch " + atom(value.c) + " {\n" + arms.map(param => "| " + param[0].c + " => " + param[1].c).join("\n") + "\n}");
}

function param(name, typ) {
  return name + ": " + typ.c;
}

function labelled(name, typ) {
  return "~" + name + ": " + typ.c;
}

function fn(params, body) {
  return make("(" + params.join(", ") + ") => " + body.c);
}

function decls(items) {
  return make(items.map(source).join("\n"));
}

let Code = {
  string: string$1,
  int: int,
  float: float,
  bool: bool,
  unit: unit,
  print: print,
  raw: raw,
  ident: ident,
  field: field$1,
  array: array,
  tuple: tuple,
  record: record$1,
  call: call,
  switch_: switch_,
  param: param,
  labelled: labelled,
  fn: fn,
  decls: decls
};

let $$var = make;

let any = {
  c: "_"
};

function string$2(value) {
  return make(JSON.stringify(value));
}

function int$1(value) {
  return make(value.toString());
}

function constructor$1(c) {
  let typed = (name, typ) => ({
    c: name,
    t: typ
  });
  if (c.fields.length !== 0) {
    let names = c.fields.map((f, i) => f.name + "$" + i.toString());
    return [
      make(c.name + "({" + c.fields.map((f, i) => f.name + ": " + names[i]).join(", ") + "})"),
      c.fields.map((f, i) => typed(names[i], f.typ))
    ];
  }
  if (c.args.length === 0) {
    return [
      make(c.name),
      []
    ];
  }
  let names$1 = c.args.map((param, i) => "arg$" + i.toString());
  return [
    make(c.name + "(" + names$1.join(", ") + ")"),
    c.args.map((typ, i) => typed(names$1[i], typ))
  ];
}

let Pat = {
  $$var: $$var,
  any: any,
  string: string$2,
  int: int$1,
  constructor: constructor$1
};

let Decl = {};

export {
  make,
  source,
  error,
  errorAt,
  typeOf,
  expected,
  readFile,
  env,
  __holeItem,
  quote,
  __quoteCode,
  __quoteDecls,
  __quoteType,
  __quotePat,
  isSimple,
  atom,
  Attr,
  Type,
  Code,
  Pat,
  Decl,
}
/* No side effect */
