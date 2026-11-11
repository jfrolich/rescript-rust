'use strict';

let Stdlib_Type = require("./Stdlib_Type.cjs");
let Primitive_option = require("./Primitive_option.cjs");

function make(source) {
  return {
    c: source
  };
}

function source(value) {
  return value.c;
}

let cat = (function (parts) {
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
});

function text(source) {
  return {
    c: source
  };
}

function build(parts) {
  return cat(parts);
}

function join(nodes, separator) {
  let parts = [];
  nodes.forEach((node, index) => {
    if (index > 0) {
      parts.push(text(separator));
    }
    parts.push(node);
  });
  return cat(parts);
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
    ...value,
    raw: true
  };
}

let quote = (function (pieces, holes, file) {
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
});

function __quoteCode(pieces, holes, file) {
  return quote(pieces, holes, file);
}

function __quoteDecls(pieces, holes, file) {
  return quote(pieces, holes, file);
}

function __quoteType(pieces, holes, file) {
  return quote(pieces, holes, file);
}

function __quotePat(pieces, holes, file) {
  return quote(pieces, holes, file);
}

function splice(items, trailing) {
  return {
    ...cat([
      join(items, ", "),
      text(trailing && items.length !== 0 ? "," : "")
    ]),
    raw: true
  };
}

function entryNodes(entries) {
  let nodes = entries.map(prim => prim);
  let isSpread = node => node.c.startsWith("...");
  let spreads = nodes.filter(isSpread);
  if (spreads.length > 1) {
    return __rescript_macro.fail("A record can have one spread, and these fields have more: " + spreads.map(node => node.c).join(", "), undefined);
  } else {
    return spreads.concat(nodes.filter(node => !node.c.startsWith("...")));
  }
}

function caseNode(param) {
  return cat([
    {
      c: "| "
    },
    param[0],
    {
      c: " => "
    },
    param[1]
  ]);
}

function __spliceItems(items, trailing) {
  return splice(items.map(prim => prim), trailing);
}

function __spliceEntries(entries, trailing) {
  return splice(entryNodes(entries), trailing);
}

function __spliceCases(cases) {
  return {
    ...join(cases.map(caseNode), "\n"),
    raw: true
  };
}

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

function atomNode(node) {
  if (isSimple(node.c)) {
    return node;
  } else {
    return cat([
      {
        c: "("
      },
      node,
      {
        c: ")"
      }
    ]);
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

function option(t) {
  return {
    c: "option<" + t.c + ">",
    o: t
  };
}

function optionOf(t) {
  let match = t.o;
  let match$1 = t.id;
  if (match !== undefined) {
    return Primitive_option.some(match);
  }
  if (match$1 === undefined) {
    return;
  }
  let inner = info(t);
  if (typeof inner !== "object" || inner.TAG !== "Option") {
    return;
  } else {
    return Primitive_option.some(inner._0);
  }
}

function declared(field) {
  let inner = optionOf(field.typ);
  if (inner !== undefined) {
    return Primitive_option.valFromOption(inner);
  } else {
    return __rescript_macro.fail("The optional field `" + field.name + "` has the type `" + field.typ.c + "`, and the type of an optional field is an option. Type.optional makes a field optional.", undefined);
  }
}

function optional(field) {
  if (field.optional) {
    return field;
  } else {
    return {
      name: field.name,
      jsName: field.jsName,
      typ: option(field.typ),
      optional: true,
      mutable_: field.mutable_,
      attrs: field.attrs
    };
  }
}

function required(field) {
  if (field.optional) {
    return {
      name: field.name,
      jsName: field.jsName,
      typ: declared(field),
      optional: false,
      mutable_: field.mutable_,
      attrs: field.attrs
    };
  } else {
    return field;
  }
}

function fieldText(field) {
  return attrText(field.attrs) + (
    field.jsName !== field.name ? "@as(" + JSON.stringify(field.jsName) + ") " : ""
  ) + (
    field.mutable_ ? "mutable " : ""
  ) + field.name + (
    field.optional ? "?: " + declared(field).c : ": " + field.typ.c
  );
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
  option: option,
  optionOf: optionOf,
  declared: declared,
  optional: optional,
  required: required,
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
  return cat([
    atomNode(value),
    text("." + name)
  ]);
}

function array(items) {
  return cat([
    {
      c: "["
    },
    join(items.map(prim => prim), ", "),
    {
      c: "]"
    }
  ]);
}

function tuple(items) {
  return cat([
    {
      c: "("
    },
    join(items.map(prim => prim), ", "),
    {
      c: ")"
    }
  ]);
}

function withAttr(value, name, payload) {
  return cat([
    text("@" + name),
    payload !== undefined ? cat([
        {
          c: "("
        },
        Primitive_option.valFromOption(payload),
        {
          c: ") "
        }
      ]) : ({
        c: " "
      }),
    atomNode(value)
  ]);
}

function entry(name, value, optionalOpt) {
  let optional = optionalOpt !== undefined ? optionalOpt : false;
  return cat([
    text(name + (
      optional ? ": ?" : ": "
    )),
    optional ? atomNode(value) : value
  ]);
}

function entryOf(field, value) {
  return entry(field.name, value, field.optional);
}

function spread(value) {
  return cat([
    {
      c: "..."
    },
    atomNode(value)
  ]);
}

function record$1(entries) {
  return cat([
    {
      c: "{"
    },
    join(entryNodes(entries), ", "),
    {
      c: "}"
    }
  ]);
}

function call(f, args) {
  return cat([
    atomNode(f),
    {
      c: "("
    },
    join(args.map(prim => prim), ", "),
    {
      c: ")"
    }
  ]);
}

function switch_(value, arms) {
  return cat([
    {
      c: "switch "
    },
    atomNode(value),
    {
      c: " {\n"
    },
    join(arms.map(caseNode), "\n"),
    {
      c: "\n}"
    }
  ]);
}

function param(name, typ) {
  return name + ": " + typ.c;
}

function labelled(name, typ) {
  return "~" + name + ": " + typ.c;
}

function fn(params, body) {
  return cat([
    text("(" + params.join(", ") + ") => "),
    body
  ]);
}

function decls(items) {
  return cat([join(items.map(prim => prim), "\n")]);
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
  withAttr: withAttr,
  entry: entry,
  entryOf: entryOf,
  spread: spread,
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
      make(c.name + "({" + c.fields.map((f, i) => f.name + (
        f.optional ? ": ?" : ": "
      ) + names[i]).join(", ") + "})"),
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

exports.make = make;
exports.source = source;
exports.cat = cat;
exports.text = text;
exports.build = build;
exports.join = join;
exports.error = error;
exports.errorAt = errorAt;
exports.typeOf = typeOf;
exports.expected = expected;
exports.readFile = readFile;
exports.env = env;
exports.__holeItem = __holeItem;
exports.quote = quote;
exports.__quoteCode = __quoteCode;
exports.__quoteDecls = __quoteDecls;
exports.__quoteType = __quoteType;
exports.__quotePat = __quotePat;
exports.splice = splice;
exports.entryNodes = entryNodes;
exports.caseNode = caseNode;
exports.__spliceItems = __spliceItems;
exports.__spliceEntries = __spliceEntries;
exports.__spliceCases = __spliceCases;
exports.isSimple = isSimple;
exports.atom = atom;
exports.atomNode = atomNode;
exports.Attr = Attr;
exports.Type = Type;
exports.Code = Code;
exports.Pat = Pat;
exports.Decl = Decl;
/* No side effect */
