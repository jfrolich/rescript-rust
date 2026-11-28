// The runner of `rescript verify` (docs/verify/law.md, docs/verify/spec.md).
//
// The compiler describes each check of a file: where its export is and, for
// a law, the shape of each parameter; for a spec, the shapes of its states
// and actions (compiler-rust/src/verify/shape.rs). This file makes values
// from the shapes, runs the checks and reports.
//
// It has no dependency and uses nothing of Node outside `main`, so a page
// can import `run` and give it its own `load` and `write`.

// ---------------------------------------------------------------------------
// Random numbers: mulberry32, seeded per check and case so that one case can
// be replayed without the ones before it.

function hashString(text, seed) {
  let h = seed >>> 0;
  for (let i = 0; i < text.length; i++) {
    h = Math.imul(h ^ text.charCodeAt(i), 0x9e3779b1);
    h = (h << 13) | (h >>> 19);
  }
  return h >>> 0;
}

function random(seed) {
  let state = seed >>> 0;
  const next = () => {
    state = (state + 0x6d2b79f5) >>> 0;
    let t = state;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return (t ^ (t >>> 14)) >>> 0;
  };
  return {
    // An integer in [0, n), n at most 2^32.
    below(n) {
      if (n <= 1) return 0;
      return Math.floor((next() / 4294967296) * n);
    },
  };
}

// ---------------------------------------------------------------------------
// Choices. A value is made from a sequence of small integers, each drawn
// with `draw(n)` from [0, n). Random testing draws them from a generator,
// exhaustive testing counts through all of them, and shrinking replays a
// shorter or smaller sequence. 0 is always the simplest choice.

class Choices {
  constructor(prefix, rng) {
    this.prefix = prefix;
    this.rng = rng;
    this.taken = [];
    this.arity = [];
  }

  draw(n) {
    const at = this.taken.length;
    let value;
    if (this.prefix !== null && at < this.prefix.length) {
      value = Math.min(this.prefix[at], n - 1);
    } else if (this.rng !== null) {
      value = this.rng.below(n);
    } else {
      value = 0;
    }
    this.taken.push(value);
    this.arity.push(n);
    return value;
  }
}

// ---------------------------------------------------------------------------
// Shapes.

const EXHAUSTIVE_LIMIT = 10000;

class Shapes {
  constructor(defs) {
    this.defs = defs;
    this.heights = new Map();
    this.sizes = new Map();
    // The least number of nested definitions a value needs: Bellman-Ford
    // over the definitions, which may refer to each other.
    const ids = Object.keys(defs).filter(id => defs[id] !== null);
    for (const id of ids) this.heights.set(id, Infinity);
    for (let round = 0; round <= ids.length; round++) {
      for (const id of ids) this.heights.set(id, this.defHeight(defs[id]));
    }
    // The definitions that contain themselves: only those need a bound on
    // how deep a value goes.
    this.recursive = new Set(ids.filter(id => this.reaches(defs[id], id, new Set())));
  }

  reaches(def, target, seen) {
    const inShape = shape => {
      switch (shape.k) {
        case "option":
        case "array":
        case "list":
        case "dict":
          return inShape(shape.of);
        case "tuple":
          return shape.of.some(inShape);
        case "poly":
          return shape.cases.some(c => c.arg !== undefined && inShape(c.arg));
        case "named":
          if (shape.id === target) return true;
          if (seen.has(shape.id)) return false;
          seen.add(shape.id);
          return this.reaches(this.defs[shape.id], target, seen);
        default:
          return false;
      }
    };
    const inFields = fields => fields.some(f => inShape(f.s));
    if (def.k === "record") return inFields(def.fields);
    return def.cases.some(c => (c.args ? c.args.some(inShape) : c.fields ? inFields(c.fields) : false));
  }

  def(shape) {
    return this.defs[shape.id];
  }

  height(shape) {
    switch (shape.k) {
      case "tuple":
        return Math.max(0, ...shape.of.map(part => this.height(part)));
      case "poly":
        return Math.min(...shape.cases.map(c => (c.arg ? this.height(c.arg) : 0)));
      case "named":
        return this.heights.get(shape.id);
      default:
        return 0;
    }
  }

  fieldsHeight(fields) {
    return Math.max(0, ...fields.filter(f => !f.opt).map(f => this.height(f.s)));
  }

  caseHeight(c) {
    if (c.args) return 1 + Math.max(0, ...c.args.map(a => this.height(a)));
    if (c.fields) return 1 + this.fieldsHeight(c.fields);
    return 0;
  }

  defHeight(def) {
    if (def.k === "record") return 1 + this.fieldsHeight(def.fields);
    return Math.min(...def.cases.map(c => this.caseHeight(c)));
  }

  // How many values a shape has; Infinity when there is no bound.
  size(shape, open = new Set()) {
    switch (shape.k) {
      case "bool":
        return 2;
      case "unit":
        return 1;
      case "option":
        return 1 + this.size(shape.of, open);
      case "tuple":
        return shape.of.reduce((n, part) => n * this.size(part, open), 1);
      case "poly":
        return shape.cases.reduce((n, c) => n + (c.arg ? this.size(c.arg, open) : 1), 0);
      case "named": {
        if (this.sizes.has(shape.id)) return this.sizes.get(shape.id);
        if (open.has(shape.id) || !this.def(shape)) return Infinity;
        open.add(shape.id);
        const def = this.def(shape);
        const fields = fs => fs.reduce((n, f) => n * this.size(f.s, open), 1);
        const size =
          def.k === "record"
            ? fields(def.fields)
            : def.cases.reduce(
                (n, c) =>
                  n +
                  (c.args
                    ? c.args.reduce((m, a) => m * this.size(a, open), 1)
                    : c.fields
                      ? fields(c.fields)
                      : 1),
                0,
              );
        open.delete(shape.id);
        this.sizes.set(shape.id, size);
        return size;
      }
      default:
        return Infinity;
    }
  }
}

// ---------------------------------------------------------------------------
// Making values.

const LETTERS =
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 _-.,:;!?/\\\"'\n\t@#$%&*+=()[]{}<>|~^`";
const SYMBOLS = ["é", "ß", "→", "日", "😀", "\u0000", "​"];
const INT_EDGES = [2147483647, 2147483646, 1073741824, 65536, 255];
const FLOAT_EDGES = [0.5, 0.1, 1e-9, 1e21, Number.MAX_SAFE_INTEGER, Number.EPSILON, 1.7976931348623157e308];

function some(value) {
  if (value === undefined) return { BS_PRIVATE_NESTED_SOME_NONE: 0 };
  if (value !== null && value.BS_PRIVATE_NESTED_SOME_NONE !== undefined) {
    return { BS_PRIVATE_NESTED_SOME_NONE: value.BS_PRIVATE_NESTED_SOME_NONE + 1 };
  }
  return value;
}

function unsome(value) {
  if (value !== null && value !== undefined && value.BS_PRIVATE_NESTED_SOME_NONE !== undefined) {
    const depth = value.BS_PRIVATE_NESTED_SOME_NONE;
    return depth === 0 ? undefined : { BS_PRIVATE_NESTED_SOME_NONE: depth - 1 };
  }
  return value;
}

function literal(lit) {
  if (lit !== null && typeof lit === "object") {
    if (lit.undefined) return undefined;
    if (lit.bigint !== undefined) return BigInt(lit.bigint);
    if (lit.float !== undefined) return Number(lit.float);
  }
  return lit;
}

class Maker {
  // `size` grows with the case number: early cases are small.
  constructor(shapes, choices, size) {
    this.shapes = shapes;
    this.c = choices;
    this.size = size;
  }

  // Whether to add one more element to a collection.
  more(depth, length) {
    if (depth <= 0 || length >= 64) return false;
    return this.c.draw(2 + (this.size >> 2)) !== 0;
  }

  int() {
    const c = this.c;
    const kind = c.draw(5);
    let magnitude;
    if (kind === 0) magnitude = c.draw(8);
    else if (kind === 1) magnitude = c.draw(256);
    else if (kind === 2) magnitude = c.draw(65536);
    else if (kind === 3) magnitude = c.draw(2147483648);
    else magnitude = INT_EDGES[c.draw(INT_EDGES.length)];
    if (c.draw(2) === 0) return magnitude;
    // -2147483648 has no positive counterpart.
    return magnitude === 2147483647 && kind === 4 ? -2147483648 : -magnitude | 0;
  }

  float() {
    const c = this.c;
    const kind = c.draw(4);
    let magnitude;
    if (kind === 0) magnitude = c.draw(16);
    else if (kind === 1) magnitude = c.draw(4096) / 8;
    else if (kind === 2) {
      const mantissa = (c.draw(67108864) * 134217728 + c.draw(134217728)) / 9007199254740992;
      magnitude = mantissa * Math.pow(10, c.draw(24) - 8);
    } else magnitude = FLOAT_EDGES[c.draw(FLOAT_EDGES.length)];
    return c.draw(2) === 0 ? magnitude : -magnitude;
  }

  character() {
    const c = this.c;
    const at = c.draw(LETTERS.length + 1);
    return at < LETTERS.length ? LETTERS[at] : SYMBOLS[c.draw(SYMBOLS.length)];
  }

  string(depth) {
    let text = "";
    let length = 0;
    while (this.more(depth, length++)) text += this.character();
    return text;
  }

  array(shape, depth) {
    const items = [];
    while (this.more(depth, items.length)) items.push(this.make(shape, depth));
    return items;
  }

  fields(fields, target, depth) {
    for (const field of fields) {
      const value = this.make(field.s, depth);
      if (!(field.opt && value === undefined)) target[field.js] = value;
    }
    return target;
  }

  make(shape, depth) {
    const c = this.c;
    switch (shape.k) {
      case "int":
        return this.int();
      case "float":
        return this.float();
      case "string":
        return this.string(1);
      case "bool":
        return c.draw(2) === 1;
      case "unit":
        return undefined;
      case "bigint":
        return BigInt(this.int()) * (c.draw(4) === 3 ? 4294967296n : 1n);
      case "char":
        return LETTERS.charCodeAt(c.draw(LETTERS.length));
      case "option":
        if (depth <= 0 && this.shapes.height(shape.of) > 0) return undefined;
        return c.draw(2) === 0 ? undefined : some(this.make(shape.of, depth));
      case "array":
        return this.array(shape.of, depth);
      case "list": {
        let list = 0;
        for (const item of this.array(shape.of, depth).reverse()) list = { hd: item, tl: list };
        return list;
      }
      case "dict": {
        const dict = {};
        let length = 0;
        while (this.more(depth, length++)) {
          const key = this.string(1);
          dict[key] = this.make(shape.of, depth);
        }
        return dict;
      }
      case "tuple":
        return shape.of.map(part => this.make(part, depth));
      case "poly": {
        const cases = this.allowed(shape.cases, depth, x => (x.arg ? this.shapes.height(x.arg) : 0));
        const chosen = cases[c.draw(cases.length)];
        return chosen.arg === undefined
          ? chosen.n
          : { NAME: chosen.n, VAL: this.make(chosen.arg, depth) };
      }
      case "named":
        return this.named(
          this.shapes.def(shape),
          this.shapes.recursive.has(shape.id) ? depth - 1 : depth,
        );
      default:
        throw new Error(`unknown shape ${JSON.stringify(shape)}`);
    }
  }

  // With no depth left, only the cases that need the fewest nested values.
  allowed(cases, depth, height) {
    if (depth > 0) return cases;
    const least = Math.min(...cases.map(height));
    return cases.filter(x => height(x) === least);
  }

  named(def, depth) {
    if (def.k === "record") {
      if (def.repr === "unboxed") return this.make(def.fields[0].s, depth);
      if (def.repr === "array") return def.fields.map(f => this.make(f.s, depth));
      return this.fields(def.fields, {}, depth);
    }
    const cases = this.allowed(def.cases, depth, x => this.shapes.caseHeight(x));
    const chosen = cases[this.c.draw(cases.length)];
    if (!chosen.args && !chosen.fields) return literal(chosen.lit);
    if (chosen.untagged) {
      return chosen.fields
        ? this.fields(chosen.fields, {}, depth)
        : this.make(chosen.args[0], depth);
    }
    const block = { [chosen.tagName]: literal(chosen.lit) };
    if (chosen.fields) return this.fields(chosen.fields, block, depth);
    chosen.args.forEach((arg, i) => {
      block["_" + i] = this.make(arg, depth);
    });
    return block;
  }
}

// ---------------------------------------------------------------------------
// Printing values as ReScript.

function kindOf(value) {
  if (value === null) return "null";
  if (Array.isArray(value)) return "array";
  return typeof value;
}

// The JavaScript kind of a shape's values, to tell untagged cases apart.
function kindOfShape(shapes, shape) {
  switch (shape.k) {
    case "int":
    case "float":
    case "char":
      return "number";
    case "string":
      return "string";
    case "bool":
      return "boolean";
    case "bigint":
      return "bigint";
    case "array":
    case "tuple":
      return "array";
    case "named": {
      const def = shapes.def(shape);
      if (def.k === "record" && def.repr === "unboxed") return kindOfShape(shapes, def.fields[0].s);
      if (def.k === "record" && def.repr === "array") return "array";
      return "object";
    }
    default:
      return "object";
  }
}

export function show(shapes, shape, value) {
  const again = (s, v) => show(shapes, s, v);
  switch (shape.k) {
    case "int":
      return String(value);
    case "float":
      if (Object.is(value, -0)) return "-0.0";
      return Number.isInteger(value) && Math.abs(value) < 1e21 ? `${value}.0` : String(value);
    case "string":
      return JSON.stringify(value);
    case "bool":
      return String(value);
    case "unit":
      return "()";
    case "bigint":
      return `${value}n`;
    case "char":
      return `'${String.fromCharCode(value)}'`;
    case "option":
      return value === undefined ? "None" : `Some(${again(shape.of, unsome(value))})`;
    case "array":
      return `[${value.map(item => again(shape.of, item)).join(", ")}]`;
    case "list": {
      const items = [];
      for (let cell = value; cell && cell.hd !== undefined; cell = cell.tl) items.push(cell.hd);
      return `list{${items.map(item => again(shape.of, item)).join(", ")}}`;
    }
    case "dict":
      return `dict{${Object.keys(value)
        .map(key => `${JSON.stringify(key)}: ${again(shape.of, value[key])}`)
        .join(", ")}}`;
    case "tuple":
      return `(${shape.of.map((part, i) => again(part, value[i])).join(", ")})`;
    case "poly": {
      if (typeof value !== "object" || value === null) return `#${value}`;
      const chosen = shape.cases.find(c => c.n === value.NAME);
      return chosen && chosen.arg ? `#${value.NAME}(${again(chosen.arg, value.VAL)})` : `#${value.NAME}`;
    }
    case "named": {
      const def = shapes.def(shape);
      return def ? showNamed(shapes, def, value) : showUnknown(value);
    }
    case "opaque":
      return showUnknown(value);
    default:
      return String(value);
  }
}

// A value whose type the compiler did not describe (an abstract type).
function showUnknown(value) {
  if (value === undefined) return "undefined";
  if (typeof value === "function") return "<function>";
  if (typeof value === "bigint") return `${value}n`;
  if (value instanceof Map) return `Map(${showUnknown([...value])})`;
  if (value instanceof Set) return `Set(${showUnknown([...value])})`;
  try {
    return JSON.stringify(value) ?? String(value);
  } catch {
    return String(value);
  }
}

function showFields(shapes, fields, value) {
  const parts = [];
  for (const field of fields) {
    if (field.opt && value[field.js] === undefined) continue;
    const shape = field.opt && field.s.k === "option" ? field.s.of : field.s;
    const shown = show(shapes, shape, field.opt ? unsome(value[field.js]) : value[field.js]);
    parts.push(`${field.n}: ${shown}`);
  }
  return `{${parts.join(", ")}}`;
}

function showNamed(shapes, def, value) {
  if (def.k === "record") {
    if (def.repr === "unboxed") {
      return `{${def.fields[0].n}: ${show(shapes, def.fields[0].s, value)}}`;
    }
    if (def.repr === "array") {
      return `{${def.fields.map((f, i) => `${f.n}: ${show(shapes, f.s, value[i])}`).join(", ")}}`;
    }
    return showFields(shapes, def.fields, value);
  }
  const constant = def.cases.find(
    c => !c.args && !c.fields && Object.is(literal(c.lit), value),
  );
  if (constant) return constant.n;
  const payload = c =>
    c.fields
      ? `${c.n}(${showFields(shapes, c.fields, value)})`
      : `${c.n}(${show(shapes, c.args[0], value)})`;
  const tagged = def.cases.find(
    c =>
      (c.args || c.fields) &&
      !c.untagged &&
      value !== null &&
      typeof value === "object" &&
      Object.is(value[c.tagName], literal(c.lit)),
  );
  if (tagged) {
    if (tagged.fields) return payload(tagged);
    return `${tagged.n}(${tagged.args.map((a, i) => show(shapes, a, value["_" + i])).join(", ")})`;
  }
  const kind = kindOf(value);
  const untagged = def.cases.find(
    c => c.untagged && (c.fields ? kind === "object" : kindOfShape(shapes, c.args[0]) === kind),
  );
  if (untagged) return payload(untagged);
  return JSON.stringify(value);
}

// ---------------------------------------------------------------------------
// Laws.

function describeError(error) {
  if (error !== null && typeof error === "object") {
    if (typeof error.RE_EXN_ID === "string") return error.RE_EXN_ID;
    if (error instanceof Error) return `${error.name}: ${error.message}`;
  }
  return String(error);
}

function smaller(a, b) {
  if (a.length !== b.length) return a.length < b.length;
  for (let i = 0; i < a.length; i++) {
    if (a[i] !== b[i]) return a[i] < b[i];
  }
  return false;
}

// Runs one law. `options`: `{ seed, cases }`.
export function checkLaw(fn, name, detail, options) {
  const shapes = new Shapes(detail.defs);
  const params = detail.params;
  let runs = 0;

  // One case: the values the choices give, and whether the law holds.
  const attempt = (choices, size) => {
    runs++;
    const maker = new Maker(shapes, choices, size);
    const depth = 2 + Math.min(4, size >> 3);
    const args = params.map(p => maker.make(p.shape, depth));
    const shown = params.map((p, i) => `${p.name} = ${show(shapes, p.shape, args[i])}`);
    let ok = false;
    let raised;
    try {
      ok = fn(...args) === true;
    } catch (error) {
      raised = describeError(error);
    }
    return { ok, raised, shown, taken: choices.taken, arity: choices.arity, size };
  };

  const shrink = failure => {
    let best = failure;
    let steps = 0;
    let budget = 3000;
    const consider = candidate => {
      if (budget-- <= 0) return false;
      const result = attempt(new Choices(candidate, null), best.size);
      if (!result.ok && smaller(result.taken, best.taken)) {
        best = result;
        steps++;
        return true;
      }
      return false;
    };
    let improved = true;
    while (improved && budget > 0) {
      improved = false;
      // Drop runs of choices: an element of a collection, a whole argument.
      for (const width of [8, 4, 2, 1]) {
        for (let at = best.taken.length - width; at >= 0; at--) {
          const candidate = best.taken.slice(0, at).concat(best.taken.slice(at + width));
          if (consider(candidate)) improved = true;
        }
      }
      // Make each choice as small as it can be.
      for (let at = 0; at < best.taken.length; at++) {
        let low = 0;
        let high = best.taken[at];
        while (low < high) {
          const middle = low + Math.floor((high - low) / 2);
          const candidate = best.taken.slice();
          candidate[at] = middle;
          if (consider(candidate)) {
            improved = true;
            high = at < best.taken.length ? Math.min(middle, best.taken[at]) : 0;
          } else {
            low = middle + 1;
          }
        }
      }
    }
    return { best, steps };
  };

  const failed = (failure, cases) => {
    const { best, steps } = shrink(failure);
    return {
      status: "failed",
      cases,
      shrinks: steps,
      counterexample: best.shown,
      raised: best.raised,
    };
  };

  // Few enough values: try them all.
  const total = params.reduce((n, p) => n * shapes.size(p.shape), 1);
  if (total <= EXHAUSTIVE_LIMIT) {
    let prefix = [];
    for (;;) {
      const result = attempt(new Choices(prefix, null), 0);
      if (!result.ok) return failed(result, runs);
      let at = result.taken.length - 1;
      while (at >= 0 && result.taken[at] + 1 >= result.arity[at]) at--;
      if (at < 0) return { status: "proved", cases: runs };
      prefix = result.taken.slice(0, at);
      prefix.push(result.taken[at] + 1);
    }
  }

  for (let i = 0; i < options.cases; i++) {
    const rng = random(hashString(`${name}#${i}`, options.seed));
    const result = attempt(new Choices(null, rng), Math.min(i, 60));
    if (!result.ok) return failed(result, i + 1);
  }
  return { status: "passed", cases: options.cases };
}

// ---------------------------------------------------------------------------
// Specs (docs/verify/spec.md): a state machine, and what must be true of it.
//
// A spec is checked by going through every state the machine can get into,
// breadth first, so the steps to a state are the fewest there are.

const PROPERTIES = ["always", "sometimes", "reachable", "eventually"];

// Stops the check of a spec: `step` or one of its functions raised.
class Stop {
  constructor(failure) {
    this.failure = failure;
  }
}

// A text that is the same for two states exactly when they are equal.
function keyOf(value) {
  switch (typeof value) {
    case "number":
      return String(value);
    case "string":
      return JSON.stringify(value);
    case "boolean":
      return value ? "t" : "f";
    case "undefined":
      return "u";
    case "bigint":
      return `${value}n`;
    case "object":
      if (value === null) return "n";
      if (Array.isArray(value)) return `[${value.map(keyOf).join(",")}]`;
      if (value instanceof Map) {
        return `M{${[...value].map(([k, v]) => `${keyOf(k)}:${keyOf(v)}`).sort().join(",")}}`;
      }
      if (value instanceof Set) return `S{${[...value].map(keyOf).sort().join(",")}}`;
      if (value instanceof Date) return `D${value.getTime()}`;
      return `{${Object.keys(value)
        .sort()
        .map(key => `${JSON.stringify(key)}:${keyOf(value[key])}`)
        .join(",")}}`;
    default:
      throw new Error(`a state holds a ${typeof value}, and states are compared`);
  }
}

// Every value of a shape that has few.
function allValues(shapes, shape) {
  const values = [];
  let prefix = [];
  for (;;) {
    const choices = new Choices(prefix, null);
    values.push(new Maker(shapes, choices, 0).make(shape, 2));
    let at = choices.taken.length - 1;
    while (at >= 0 && choices.taken[at] + 1 >= choices.arity[at]) at--;
    if (at < 0) return values;
    prefix = choices.taken.slice(0, at);
    prefix.push(choices.taken[at] + 1);
  }
}

// Checks one spec. `options`: `{ states }`, the most states to go through.
// The result has `failures` (`{property, heading, trace}`) and a `summary`
// of what holds.
export function checkSpec(spec, name, detail, options) {
  const shapes = new Shapes(detail.defs);
  const limit = options.states ?? 100000;
  const properties = PROPERTIES.filter(property => typeof spec[property] === "function");
  const failures = [];
  const fail = (property, heading, trace = []) => failures.push({ property, heading, trace });
  const steps = n => (n === 0 ? "in the first state" : `after ${plural(n, "step")}`);

  // states[i] is `{value, parent, action, depth}`; edges[i] is the states it
  // goes to, each with the first action that leads there.
  const states = [];
  const edges = [];
  const index = new Map();
  let complete = true;

  const showAction = action => show(shapes, detail.action, action);
  const line = (label, state) => ({ label, state: show(shapes, detail.state, state) });
  // The lines of a run: `path` is a list of `{action, to}` from the first state.
  const render = groups => {
    const width = Math.max(4, ...groups.flatMap(g => (g.rows ?? []).map(row => row.label.length)));
    const out = [];
    for (const group of groups) {
      if (group.text !== undefined) out.push(group.text);
      for (const row of group.rows ?? []) {
        out.push(`${row.label.padEnd(width)}  ${row.first ? " " : "→"}  ${row.state}`);
      }
    }
    return out;
  };
  const pathTo = (i, parents = states) => {
    const rows = [];
    for (let at = i; at !== -1; at = parents[at].parent) {
      const { parent, action } = parents[at];
      rows.push(
        parent === -1
          ? { ...line("init", states[at].value), first: true }
          : line(showAction(action), states[at].value),
      );
    }
    return rows.reverse();
  };
  // Runs a function of the spec in state `i`; `action` is the one `step`
  // was given.
  const guarded = (what, i, run, action) => {
    try {
      return run();
    } catch (error) {
      const raised = describeError(error);
      const rows = pathTo(i);
      if (action !== undefined) rows.push({ label: showAction(action), state: `raises ${raised}` });
      throw new Stop({
        property: what,
        heading: `\`${what}\` raised ${raised} ${steps(states[i].depth)}:`,
        trace: render([{ rows }]),
      });
    }
  };
  const holds = (property, i) => guarded(property, i, () => spec[property](states[i].value) === true);

  try {
    if (typeof spec.step !== "function") {
      throw new Stop({ property: "step", heading: "the spec has no `step`", trace: [] });
    }
    let everyAction = null;
    if (typeof spec.actions !== "function") {
      if (!(shapes.size(detail.action) <= EXHAUSTIVE_LIMIT)) {
        throw new Stop({
          property: "actions",
          heading:
            "the actions cannot be listed: the action type has too many values. Give the spec `actions: state => [...]`.",
          trace: [],
        });
      }
      everyAction = allValues(shapes, detail.action);
    }

    const add = (value, parent, action) => {
      const key = keyOf(value);
      const known = index.get(key);
      if (known !== undefined) return known;
      if (states.length >= limit) {
        complete = false;
        return -1;
      }
      const i = states.length;
      index.set(key, i);
      states.push({ value, parent, action, depth: parent === -1 ? 0 : states[parent].depth + 1 });
      edges.push([]);
      return i;
    };

    add(spec.init, -1, undefined);
    let alwaysHolds = true;
    for (let i = 0; i < states.length; i++) {
      const state = states[i].value;
      if (alwaysHolds && properties.includes("always") && !holds("always", i)) {
        alwaysHolds = false;
        fail("always", `\`always\` is false ${steps(states[i].depth)}:`, render([{ rows: pathTo(i) }]));
        // Nothing else to find out: stop here.
        if (properties.length === 1) break;
      }
      const actions = everyAction ?? guarded("actions", i, () => spec.actions(state));
      if (!Array.isArray(actions)) {
        throw new Stop({ property: "actions", heading: "`actions` did not give an array", trace: [] });
      }
      const seen = new Set();
      for (const action of actions) {
        const next = guarded("step", i, () => spec.step(state, action), action);
        const to = guarded("step", i, () => add(next, i, action), action);
        if (to !== -1 && !seen.has(to)) {
          seen.add(to);
          edges[i].push({ to, action });
        }
      }
    }

    const count = states.length;
    const undecided = property =>
      fail(
        property,
        `\`${property}\` was not decided: the machine has more than ${count} states. Give it fewer, or raise --states.`,
      );

    if (properties.includes("sometimes")) {
      let found = false;
      for (let i = 0; i < count && !found; i++) found = holds("sometimes", i);
      if (!found && complete) {
        fail("sometimes", `\`sometimes\` is true in none of the ${plural(count, "state")} the machine can get into`);
      } else if (!found) undecided("sometimes");
    }

    if (properties.includes("reachable")) {
      if (!complete) undecided("reachable");
      else {
        // Backwards from the states where it is true.
        const back = states.map(() => []);
        edges.forEach((targets, from) => targets.forEach(({ to }) => back[to].push(from)));
        const can = new Uint8Array(count);
        const queue = [];
        for (let i = 0; i < count; i++) {
          if (holds("reachable", i)) {
            can[i] = 1;
            queue.push(i);
          }
        }
        for (let at = 0; at < queue.length; at++) {
          for (const from of back[queue[at]]) {
            if (!can[from]) {
              can[from] = 1;
              queue.push(from);
            }
          }
        }
        const lost = can.indexOf(0);
        if (lost !== -1) {
          fail(
            "reachable",
            `\`reachable\` is out of reach ${steps(states[lost].depth)}: no actions lead from the last state to one where it is true`,
            render([{ rows: pathTo(lost) }]),
          );
        }
      }
    }

    if (properties.includes("eventually")) {
      if (!complete) undecided("eventually");
      else {
        const run = neverReaching(i => holds("eventually", i), states, edges);
        if (run !== null) {
          const prefix = { rows: pathTo(run.end, run.parents) };
          if (run.loop === null) {
            fail(
              "eventually",
              "`eventually` is never true in this run, which ends: no action changes its last state",
              render([prefix]),
            );
          } else {
            const rows = run.loop.map(({ to, action }) => line(showAction(action), states[to].value));
            fail(
              "eventually",
              "`eventually` is never true in this run, which can go on forever:",
              render([prefix, { text: "and then, again and again:", rows }]),
            );
          }
        }
      }
    }
  } catch (stop) {
    if (!(stop instanceof Stop)) throw stop;
    failures.push(stop.failure);
  }

  const count = states.length;
  const names = properties.join(", ");
  const verb = properties.length === 1 ? "holds" : "hold";
  const summary = complete
    ? `${names} ${verb} over all ${plural(count, "state")}`
    : `${names} held over the first ${plural(count, "state")} (there are more)`;
  return { failures, summary, states: count, complete };
}

// A run that never gets to a state where `holds`: one that ends (no action
// changes its last state) or one that goes round. `null` when every run
// gets there. An action that leaves the state as it is, is no step.
function neverReaching(holds, states, edges) {
  const count = states.length;
  if (holds(0)) return null;
  // The states a run can be in before it gets there, with the fewest steps
  // to each that stay among them.
  const parents = states.map(() => null);
  parents[0] = { parent: -1, action: undefined, depth: 0 };
  const order = [0];
  const truth = new Int8Array(count).fill(-1);
  truth[0] = 0;
  const before = i => {
    if (truth[i] === -1) truth[i] = holds(i) ? 1 : 0;
    return truth[i] === 0;
  };
  for (let at = 0; at < order.length; at++) {
    const from = order[at];
    for (const { to, action } of edges[from]) {
      if (to !== from && parents[to] === null && before(to)) {
        parents[to] = { parent: from, action, depth: parents[from].depth + 1 };
        order.push(to);
      }
    }
  }
  const among = i => parents[i] !== null;
  const moves = i => edges[i].filter(edge => edge.to !== i);

  // A run that ends.
  let best = null;
  for (const i of order) {
    if (moves(i).length === 0) {
      best = { end: i, parents, loop: null, length: parents[i].depth };
      break;
    }
  }

  // A run that goes round: a state that leads back to itself.
  const color = new Uint8Array(count);
  let onLoop = -1;
  for (const root of order) {
    if (color[root] !== 0 || onLoop !== -1) continue;
    const stack = [{ node: root, next: 0 }];
    color[root] = 1;
    while (stack.length > 0 && onLoop === -1) {
      const top = stack[stack.length - 1];
      const targets = moves(top.node).filter(edge => among(edge.to));
      if (top.next >= targets.length) {
        color[top.node] = 2;
        stack.pop();
        continue;
      }
      const { to } = targets[top.next++];
      if (color[to] === 1) {
        // The states of the loop: of those, start from the nearest one.
        const at = stack.findIndex(frame => frame.node === to);
        onLoop = stack
          .slice(at)
          .map(frame => frame.node)
          .reduce((a, b) => (parents[b].depth < parents[a].depth ? b : a));
      } else if (color[to] === 0) {
        color[to] = 1;
        stack.push({ node: to, next: 0 });
      }
    }
  }
  if (onLoop !== -1) {
    // The shortest way from that state back to itself.
    const via = new Map([[onLoop, null]]);
    const queue = [onLoop];
    let last = null;
    for (let at = 0; at < queue.length && last === null; at++) {
      const from = queue[at];
      for (const edge of moves(from)) {
        if (!among(edge.to)) continue;
        if (edge.to === onLoop) {
          last = { from, edge };
          break;
        }
        if (!via.has(edge.to)) {
          via.set(edge.to, { from, edge });
          queue.push(edge.to);
        }
      }
    }
    const loop = [last.edge];
    for (let step = via.get(last.from); step !== null; step = via.get(step.from)) loop.push(step.edge);
    loop.reverse();
    const length = parents[onLoop].depth + loop.length;
    if (best === null || length < best.length) best = { end: onLoop, parents, loop, length };
  }
  return best;
}

// ---------------------------------------------------------------------------
// The report.

function painter(color) {
  const paint = code => text => (color ? `\u001b[${code}m${text}\u001b[0m` : text);
  return { green: paint(32), red: paint(31), dim: paint(2), bold: paint(1) };
}

export function lookup(module, path) {
  const from = root => {
    let value = root;
    for (const name of path) {
      if (value === null || value === undefined) return undefined;
      value = value[name] !== undefined ? value[name] : value["$$" + name];
    }
    return value;
  };
  const found = from(module);
  return found !== undefined || module.default === undefined ? found : from(module.default);
}

function plural(n, word) {
  return `${n} ${word}${n === 1 ? "" : "s"}`;
}

// Runs every check of the manifest and returns the number that failed.
// `host.load(file)` gives a compiled module, `host.write(text)` prints.
export async function run(manifest, host) {
  const paint = painter(manifest.color);
  const options = { seed: manifest.seed >>> 0, cases: manifest.cases, states: manifest.states };
  const out = text => host.write(text + "\n");
  let checked = 0;
  let failed = 0;
  for (const module of manifest.modules) {
    out(paint.bold(module.source));
    let loaded;
    try {
      loaded = await host.load(module.file);
    } catch (error) {
      failed += module.items.length;
      checked += module.items.length;
      out(`  ${paint.red("✗")} the module could not be loaded: ${describeError(error)}`);
      continue;
    }
    const width = Math.max(...module.items.map(item => item.path.join(".").length));
    for (const item of module.items) {
      const name = item.path.join(".");
      const label = name.padEnd(width + 2);
      const value = lookup(loaded, item.path);
      checked++;
      if (value === undefined) {
        failed++;
        out(`  ${paint.red("✗")} ${label}is not exported by the compiled module`);
        continue;
      }
      const lines = [];
      const result = runItem(item, name, value, options, lines);
      if (result.ok) {
        out(`  ${paint.green("✓")} ${label}${paint.dim(result.summary)}`);
      } else {
        failed++;
        out(`  ${paint.red("✗")} ${label}${result.summary}`);
        for (const line of lines) out(`      ${line}`);
        out(paint.dim(`      ${module.source}:${item.line}`));
      }
    }
    out("");
  }
  if (failed === 0) {
    out(paint.green(`${plural(checked, "check")} passed`));
  } else {
    out(paint.red(`${failed} of ${plural(checked, "check")} failed`) + paint.dim(` (seed ${options.seed})`));
  }
  return failed;
}

// How the compiler proved a law (docs/verify/proof.md).
function howProved(proof) {
  const parts = [];
  if (proof.induction.length > 0) parts.push(`induction on ${proof.induction.join(", ")}`);
  else if (proof.cases > 1) parts.push(`${proof.cases} cases`);
  else parts.push("by computation");
  if (proof.lemmas.length > 0) parts.push(`using ${proof.lemmas.join(", ")}`);
  return parts.join(", ");
}

export function runItem(item, name, value, options, lines) {
  if (item.kind === "law") {
    // A law the compiler proved is run all the same: the run checks the
    // prover against the program as it is compiled.
    const result = checkLaw(value, name, item.detail, options);
    const proof = item.detail.proof;
    const proved = proof !== undefined && proof.status === "proved";
    if (result.status === "failed") {
      for (const line of result.counterexample) lines.push(line);
      lines.push(result.raised === undefined ? "the law returned false" : `the law raised ${result.raised}`);
      if (proved) lines.push("rescript proved this law, and this run breaks it: that is a bug in rescript, please report it");
      const shrunk = result.shrinks > 0 ? `, made smaller ${plural(result.shrinks, "time")}` : "";
      return { ok: false, summary: `fails (case ${result.cases}${shrunk})` };
    }
    if (result.status === "proved") {
      return { ok: true, summary: `holds for all ${plural(result.cases, "value")}` };
    }
    if (proved) return { ok: true, summary: `proved for every value (${howProved(proof)})` };
    const ran = `held for ${plural(result.cases, "random case")}`;
    const reason = proof === undefined ? "this run did not look for one" : proof.reason;
    if (item.detail.must) {
      lines.push(`${ran}, which is not a proof`);
      lines.push(`no proof was found: ${reason}`);
      return { ok: false, summary: "is not proved" };
    }
    return { ok: true, summary: proof === undefined ? ran : `${ran} (no proof: ${reason})` };
  }
  if (item.kind === "spec") {
    const result = checkSpec(value, name, item.detail, options);
    if (result.failures.length === 0) return { ok: true, summary: result.summary };
    for (const failure of result.failures) {
      lines.push(failure.heading);
      for (const line of failure.trace) lines.push(`  ${line}`);
    }
    return { ok: false, summary: `fails: ${result.failures.map(failure => failure.property).join(", ")}` };
  }
  lines.push(`this version of rescript cannot run a ${item.kind}`);
  return { ok: false, summary: "was not run" };
}

// ---------------------------------------------------------------------------
// `node runner.mjs manifest.json`

export async function main(argv) {
  const { readFileSync } = await import("node:fs");
  const { pathToFileURL } = await import("node:url");
  const manifest = JSON.parse(readFileSync(argv[0], "utf8"));
  const failed = await run(manifest, {
    load: file => import(pathToFileURL(file).href),
    write: text => process.stdout.write(text),
  });
  process.exitCode = failed === 0 ? 0 : 1;
}

if (typeof process !== "undefined" && process.argv && process.argv[1] && import.meta.url.endsWith(process.argv[1].split(/[\\/]/).pop())) {
  await main(process.argv.slice(2));
}
