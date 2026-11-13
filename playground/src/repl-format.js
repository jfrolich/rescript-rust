/**
 * A JavaScript value as the ReScript that makes it.
 *
 * At run time `Some(3)` is `3`, `Red` is `"Red"` and `Circle(1.)` an object
 * tagged `TAG`, so the value alone does not say what it is. The compiler
 * gives the shape of the value's type (`signature` of a compilation, see
 * `repl::describe_signature` in the compiler): `shape` is the type one level
 * deep, `defs` the records and variants it refers to with `{k: "ref", id}`.
 */

const WIDTH = 80;
const MAX_DEPTH = 24;
const MAX_ITEMS = 100;

/** `value` as source text, broken over lines when it is wider than a line. */
export function formatValue(value, shape, defs, indent = 0) {
  return render(describe(value, shape, defs, 0), indent);
}

// A value is text, or a group `open item, item close` that is written on one
// line when it fits.
function group(open, items, close) {
  return { open, items, close };
}

function flat(node) {
  if (typeof node === "string") return node;
  return node.open + node.items.map(flat).join(", ") + node.close;
}

function render(node, indent) {
  if (typeof node === "string") return node;
  const line = flat(node);
  if (indent + line.length <= WIDTH || node.items.length === 0) return line;
  const inner = " ".repeat(indent + 2);
  const items = node.items.map((item) => `${inner}${render(item, indent + 2)},\n`);
  return `${node.open}\n${items.join("")}${" ".repeat(indent)}${node.close}`;
}

/** `key: value`, where the value may be a group. */
function entry(key, node) {
  if (typeof node === "string") return `${key}: ${node}`;
  return { ...node, open: `${key}: ${node.open}` };
}

/** `Name(arguments)`. */
function apply(name, nodes) {
  if (nodes.length === 0) return name;
  // `Some({...})` reads better than a record on a line of its own.
  if (nodes.length === 1 && typeof nodes[0] !== "string") {
    return { ...nodes[0], open: `${name}(${nodes[0].open}`, close: `${nodes[0].close})` };
  }
  return group(`${name}(`, nodes, ")");
}

function limited(values, each) {
  const nodes = values.slice(0, MAX_ITEMS).map(each);
  if (values.length > MAX_ITEMS) nodes.push(`… ${values.length - MAX_ITEMS} more`);
  return nodes;
}

function float(value) {
  if (Number.isInteger(value)) return Object.is(value, -0) ? "-0." : `${value}.`;
  if (Number.isNaN(value)) return "nan";
  if (value === Infinity) return "infinity";
  if (value === -Infinity) return "neg_infinity";
  return String(value);
}

function describe(value, shape, defs, depth) {
  if (depth > MAX_DEPTH) return "…";
  const next = (inner, of) => describe(inner, of, defs, depth + 1);
  switch (shape?.k) {
    case "int":
      return typeof value === "number" ? String(value) : javascript(value, depth);
    case "float":
      return typeof value === "number" ? float(value) : javascript(value, depth);
    case "string":
      return typeof value === "string" ? JSON.stringify(value) : javascript(value, depth);
    case "bool":
      return String(value);
    case "unit":
      return "()";
    case "bigint":
      return typeof value === "bigint" ? `${value}n` : javascript(value, depth);
    case "char":
      return typeof value === "number" ? `'${String.fromCodePoint(value)}'` : javascript(value, depth);
    case "fn":
      return "<fun>";
    case "promise":
      return "<promise>";
    case "option": {
      if (value === undefined) return "None";
      // `Some(None)` cannot be `undefined`: it is an object that counts the
      // options around the `None`.
      const nested = value !== null && typeof value === "object" ? value.BS_PRIVATE_NESTED_SOME_NONE : undefined;
      if (nested !== undefined) {
        return apply("Some", [next(nested === 0 ? undefined : { BS_PRIVATE_NESTED_SOME_NONE: nested - 1 }, shape.of)]);
      }
      return apply("Some", [next(value, shape.of)]);
    }
    case "array":
      if (!Array.isArray(value)) return javascript(value, depth);
      return group("[", limited(value, (item) => next(item, shape.of)), "]");
    case "tuple":
      if (!Array.isArray(value)) return javascript(value, depth);
      return group("(", shape.of.map((of, index) => next(value[index], of)), ")");
    case "list": {
      const items = [];
      let cell = value;
      while (cell !== null && typeof cell === "object" && "hd" in cell && items.length <= MAX_ITEMS) {
        items.push(cell.hd);
        cell = cell.tl;
      }
      return group("list{", limited(items, (item) => next(item, shape.of)), "}");
    }
    case "dict": {
      if (value === null || typeof value !== "object") return javascript(value, depth);
      const keys = Object.keys(value);
      return group("dict{", limited(keys, (key) => entry(JSON.stringify(key), next(value[key], shape.of))), "}");
    }
    case "result": {
      if (value === null || typeof value !== "object") return javascript(value, depth);
      return value.TAG === "Ok" ? apply("Ok", [next(value._0, shape.ok)]) : apply("Error", [next(value._0, shape.error)]);
    }
    case "poly": {
      if (value !== null && typeof value === "object" && "NAME" in value) {
        const found = shape.cases.find((candidate) => candidate.name === String(value.NAME));
        return apply(`#${polyName(value.NAME)}`, [next(value.VAL, found?.of ?? null)]);
      }
      return `#${polyName(value)}`;
    }
    case "ref":
      return declared(value, defs[shape.id], defs, depth);
    default:
      // A lazy value is an object that says whether it has run.
      if (value !== null && typeof value === "object" && "LAZY_DONE" in value) return "<lazy>";
      return javascript(value, depth);
  }
}

function polyName(name) {
  const text = String(name);
  return /^[A-Za-z_][A-Za-z0-9_']*$|^[0-9]+$/.test(text) ? text : JSON.stringify(text);
}

function fields(value, list, defs, depth) {
  const nodes = [];
  for (const field of list) {
    const item = value[field.js];
    if (field.optional && item === undefined) continue;
    nodes.push(entry(field.name, describe(item, field.of, defs, depth + 1)));
  }
  return group("{", nodes, "}");
}

function isLiteral(value, tag) {
  switch (tag.t) {
    case "null":
      return value === null;
    case "undefined":
      return value === undefined;
    case "bigint":
      return typeof value === "bigint" && String(value) === tag.v;
    default:
      return typeof value === tag.t && value === tag.v;
  }
}

/** Whether a value can be the payload of a constructor without a tag. */
function fits(value, shape, defs) {
  const kind = shape?.k === "ref" ? defs[shape.id]?.k : shape?.k;
  switch (kind) {
    case "int":
    case "float":
      return typeof value === "number";
    case "string":
      return typeof value === "string";
    case "bool":
      return typeof value === "boolean";
    case "bigint":
      return typeof value === "bigint";
    case "array":
    case "tuple":
      return Array.isArray(value);
    case "fn":
      return typeof value === "function";
    case "record":
    case "dict":
      return value !== null && typeof value === "object" && !Array.isArray(value);
    default:
      return true;
  }
}

function declared(value, def, defs, depth) {
  if (!def) return javascript(value, depth);
  if (def.k === "record") {
    // An unboxed record is its one field.
    if (def.unboxed && def.fields.length === 1) {
      return group("{", [entry(def.fields[0].name, describe(value, def.fields[0].of, defs, depth + 1))], "}");
    }
    if (value === null || typeof value !== "object") return javascript(value, depth);
    return fields(value, def.fields, defs, depth);
  }
  const payload = (found, object) => {
    if (found.fields) return apply(found.name, [fields(object, found.fields, defs, depth)]);
    return apply(found.name, found.args.map((of, index) => describe(object[`_${index}`], of, defs, depth + 1)));
  };
  const constant = def.cases.find((candidate) => candidate.constant && isLiteral(value, candidate.tag));
  if (constant) return constant.name;
  if (value !== null && typeof value === "object") {
    const tagged = def.cases.find(
      (candidate) => !candidate.constant && !candidate.untagged && isLiteral(value[candidate.tagName], candidate.tag),
    );
    if (tagged) return payload(tagged, value);
  }
  // A constructor without a tag is its payload: the first one it can be.
  const untagged = def.cases.filter((candidate) => candidate.untagged);
  const found =
    untagged.find((candidate) =>
      candidate.fields ? value !== null && typeof value === "object" : fits(value, candidate.args[0], defs),
    ) ?? untagged[0];
  if (!found) return javascript(value, depth);
  if (found.fields) return apply(found.name, [fields(value, found.fields, defs, depth)]);
  return apply(found.name, [describe(value, found.args[0], defs, depth + 1)]);
}

/**
 * A value whose type says nothing about its representation (an abstract
 * type, a type variable, a JavaScript object), as JavaScript.
 */
function javascript(value, depth) {
  if (depth > MAX_DEPTH) return "…";
  if (value === undefined) return "undefined";
  if (value === null) return "null";
  switch (typeof value) {
    case "string":
      return JSON.stringify(value);
    case "bigint":
      return `${value}n`;
    case "function":
      return "<fun>";
    case "symbol":
      return value.toString();
    case "object":
      break;
    default:
      return String(value);
  }
  const next = (inner) => javascript(inner, depth + 1);
  if (Array.isArray(value)) return group("[", limited(value, next), "]");
  if (value instanceof Date) return Number.isNaN(value.getTime()) ? "Date(invalid)" : `Date(${value.toISOString()})`;
  if (value instanceof RegExp) return String(value);
  if (value instanceof Error) return `${value.name}(${JSON.stringify(value.message)})`;
  if (value instanceof Promise) return "<promise>";
  if (value instanceof Map) {
    return group("Map{", limited([...value.entries()], ([key, item]) => entry(flat(next(key)), next(item))), "}");
  }
  if (value instanceof Set) return group("Set{", limited([...value.values()], next), "}");
  // An exception of ReScript.
  if (typeof value.RE_EXN_ID === "string") {
    const args = Object.keys(value)
      .filter((key) => /^_\d+$/.test(key))
      .map((key) => next(value[key]));
    return apply(exceptionName(value.RE_EXN_ID), args);
  }
  const keys = Object.keys(value);
  return group("{", limited(keys, (key) => entry(/^[A-Za-z_$][\w$]*$/.test(key) ? key : JSON.stringify(key), next(value[key]))), "}");
}

/** `Module.Name/3` is `Name` of a module that is opened, or of this file. */
function exceptionName(id) {
  const name = id.replace(/\/\d+$/, "");
  return hiddenModules ? name.replace(hiddenModules, "") : name;
}

let hiddenModules = null;

/**
 * Leave the modules whose name matches `pattern` (a prefix with its dot)
 * out of the names of exceptions: the files of a read-eval-print loop.
 */
export function hideModules(pattern) {
  hiddenModules = pattern;
}

/** What was raised, for the line under an input that failed. */
export function formatException(error) {
  if (error !== null && typeof error === "object" && typeof error.RE_EXN_ID === "string") {
    // `throw` of a JavaScript error is wrapped.
    if (error.RE_EXN_ID === "JsExn" && error._1 !== undefined) return formatException(error._1);
    return flat(javascript(error, 0));
  }
  if (error instanceof Error) return `${error.name}: ${error.message}`;
  return flat(javascript(error, 0));
}
