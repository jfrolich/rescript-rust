/**
 * Completion: what can be written at a place in a file.
 *
 * The compiler has no completion of its own, so the answers come from
 * compiling small files with it:
 *
 * - the members of a module are what a file `include Path` defines;
 * - the names in scope are what the file up to the item being written
 *   defines, and the members of what it opens;
 * - the type of the expression before a `.` or a `->` is what the compiler
 *   says when that expression is given a type it cannot have, in the place
 *   where it is written, so that function parameters and other local names
 *   have their types. From that type come the fields of a record, and the
 *   functions that take it first, for a pipe.
 *
 * This file has no dependency on the page: `contextAt` is the lexical half,
 * `createCompleter` the half that asks the compiler.
 */

const KEYWORDS = [
  "and", "as", "assert", "async", "await", "catch", "constraint", "else", "exception", "external", "false", "for",
  "if", "in", "include", "let", "module", "mutable", "of", "open", "private", "rec", "switch", "true", "try",
  "type", "when", "while", "with",
];
const KEYWORD_SET = new Set(KEYWORDS);
// After these a name is being given, not used.
const BINDERS = new Set(["let", "rec", "type", "module", "exception", "external", "and", "as", "open", "include"]);
// A line that starts with one of these continues the item before it.
const CONTINUES = /^(?:and|else|catch)\b/;
const CLOSERS = { "(": ")", "[": "]", "{": "}" };

/**
 * The tokens of `text`, the brackets that are open at its end, and the
 * offsets where a top-level item starts. `inside` is "string" or "comment"
 * when the text ends in one.
 */
export function tokenize(text) {
  const tokens = [];
  const stack = [];
  const starts = [];
  let inside = null;
  const length = text.length;
  const consider = (at) => {
    const char = text[at];
    if (char === undefined || /\s/.test(char) || ")]}|.,:?&+*/<>=-".includes(char)) return;
    if (CONTINUES.test(text.slice(at, at + 6))) return;
    starts.push(at);
  };
  const push = (t, s, e, extra) => tokens.push({ t, s, e, v: text.slice(s, e), ...extra });
  consider(0);
  let i = 0;
  while (i < length) {
    const char = text[i];
    if (char === "\n") {
      if (stack.length === 0) consider(i + 1);
      i += 1;
    } else if (/\s/.test(char)) {
      i += 1;
    } else if (text.startsWith("//", i)) {
      const end = text.indexOf("\n", i);
      if (end < 0) {
        inside = "comment";
        break;
      }
      i = end;
    } else if (text.startsWith("/*", i)) {
      let open = 1;
      i += 2;
      while (i < length && open > 0) {
        if (text.startsWith("/*", i)) (open += 1), (i += 2);
        else if (text.startsWith("*/", i)) (open -= 1), (i += 2);
        else i += 1;
      }
      if (open > 0) {
        inside = "comment";
        break;
      }
    } else if (char === '"' || char === "`") {
      const start = i;
      i += 1;
      while (i < length && text[i] !== char) i += text[i] === "\\" ? 2 : 1;
      if (i >= length) {
        inside = "string";
        break;
      }
      i += 1;
      push("str", start, i);
    } else if (char === "'") {
      const literal = /^'(?:\\[^']*|[^\\'])'/.exec(text.slice(i, i + 12));
      const variable = /^'[A-Za-z_][A-Za-z0-9_]*/.exec(text.slice(i, i + 64));
      const end = i + (literal ? literal[0].length : variable ? variable[0].length : 1);
      push(literal ? "str" : variable ? "tv" : "op", i, end);
      i = end;
    } else if (/[0-9]/.test(char)) {
      const number = /^\d[\d_]*(?:\.[\d_]*)?(?:[eE][+-]?\d+)?n?/.exec(text.slice(i, i + 64));
      push("num", i, i + number[0].length);
      i += number[0].length;
    } else if (/[A-Za-z_]/.test(char)) {
      let end = i + 1;
      while (end < length && /[A-Za-z0-9_']/.test(text[end])) end += 1;
      push(/[A-Z]/.test(char) ? "up" : "id", i, end);
      i = end;
    } else if ("([{".includes(char)) {
      stack.push(tokens.length);
      push("open", i, i + 1);
      i += 1;
    } else if (")]}".includes(char)) {
      const match = stack.length > 0 ? stack.pop() : -1;
      push("close", i, i + 1, { match });
      i += 1;
    } else {
      const end = text.startsWith("->", i) || text.startsWith("=>", i) ? i + 2 : text.startsWith("...", i) ? i + 3 : i + 1;
      push("op", i, end);
      i = end;
    }
  }
  return { tokens, stack, starts, inside };
}

/**
 * The token an expression that ends with the token `k` starts with: names
 * and literals joined by `.` and `->`, with their calls and brackets. -1
 * when no expression ends there.
 */
function operandStart(tokens, k) {
  let i = k;
  for (;;) {
    const token = tokens[i];
    if (!token) return -1;
    if (token.t === "close") {
      if (token.match < 0) return -1;
      i = token.match;
      // `f(x)`, `list{...}`: what is called or indexed.
      const before = tokens[i - 1];
      if (before && before.e === tokens[i].s && (before.t === "id" || before.t === "up" || before.t === "close")) {
        i -= 1;
        continue;
      }
    } else if (!["id", "up", "num", "str"].includes(token.t)) {
      return -1;
    } else if (token.t === "id" && KEYWORD_SET.has(token.v) && token.v !== "true" && token.v !== "false") {
      return -1;
    }
    const joint = tokens[i - 1];
    if (joint && joint.t === "op" && (joint.v === "." || joint.v === "->") && tokens[i - 2]) {
      i -= 2;
      continue;
    }
    if (joint && joint.t === "op" && joint.v === "#" && joint.e === tokens[i].s) return i - 1;
    return i;
  }
}

/**
 * What is being written at `offset` of `source`:
 *
 * - `{kind: "member", path, sigil}` after `Path.`, with the `%` or `@`
 *   before the path;
 * - `{kind: "field", operand}` after `expression.`;
 * - `{kind: "pipe", operand}` after `expression->`;
 * - `{kind: "sigil", sigil}` after `%` or `@`;
 * - `{kind: "name"}` for a name.
 *
 * `from` is where the word being written starts and `partial` that word;
 * `start` is where the top-level item around it starts; `operand` is the
 * range of the expression and `closers` what closes the brackets that are
 * open there. Null inside a string or a comment, and where a name is given.
 */
export function contextAt(source, offset) {
  const { tokens, stack, starts, inside } = tokenize(source.slice(0, offset));
  if (inside) return null;

  // The item starts at the last line that starts one; an attribute on a
  // line of its own belongs to the item below it.
  let at = starts.length - 1;
  while (at > 0 && /^(?:@@?[A-Za-z_][\w.]*(?:\([^()]*\))?\s*)+$/.test(source.slice(starts[at - 1], starts[at]))) at -= 1;
  const start = starts[at] ?? 0;

  let last = tokens.length - 1;
  let partial = "";
  let from = offset;
  const word = tokens[last];
  if (word && (word.t === "id" || word.t === "up") && word.e === offset) {
    partial = word.v;
    from = word.s;
    last -= 1;
  }
  const base = { from, partial, start };
  const prev = tokens[last];
  const sigilBefore = (index) => {
    const token = tokens[index];
    const next = tokens[index + 1];
    if (!token || token.t !== "op" || !next || token.e !== next.s) return null;
    return token.v === "%" || token.v === "@" ? token.v : null;
  };
  const withOperand = (kind, end) => {
    const first = operandStart(tokens, end);
    if (first < 0 || tokens[first].s < start) return null;
    const closers = stack
      .map((index) => CLOSERS[tokens[index].v])
      .reverse()
      .join("");
    return { ...base, kind, operand: { s: tokens[first].s, e: tokens[end].e }, closers };
  };

  if (prev && prev.t === "op" && prev.v === "." && prev.e === from) {
    // A module path: `Json.`, `Intl.NumberFormat.`.
    const segments = [];
    let index = last - 1;
    while (tokens[index]?.t === "up" && tokens[index].e === tokens[index + 1].s) {
      segments.unshift(tokens[index].v);
      const dot = tokens[index - 1];
      if (dot?.t === "op" && dot.v === "." && tokens[index - 2]?.t === "up") index -= 2;
      else break;
    }
    if (segments.length > 0) {
      const before = tokens[index - 1];
      const isField = before?.t === "op" && before.v === "." && before.e === tokens[index].s;
      if (!isField) return { ...base, kind: "member", path: segments.join("."), sigil: sigilBefore(index - 1) };
    }
    return withOperand("field", last - 1);
  }
  if (prev && prev.t === "op" && prev.v === "->") return withOperand("pipe", last - 1);
  if (prev && prev.t === "op" && prev.e === from) {
    if (prev.v === "%" || prev.v === "@") return { ...base, kind: "sigil", sigil: prev.v };
    if (prev.v === "~" || prev.v === "#") return null;
  }
  if (prev && prev.t === "id" && BINDERS.has(prev.v)) return null;
  return { ...base, kind: "name" };
}

// ── Reading what the compiler printed ───────────────────────────────────────

const SCRATCH = /\b(?:Repl\d+(?:_open\d+)?|Complete__[HP]\d*)\./g;

function stripAnsi(text) {
  return text.replace(/\u001b\[[0-9;]*m/g, "");
}

function oneLine(text) {
  return text.replace(/\s+/g, " ").trim();
}

/** The type of a value from its declaration: `let f: t`, `@send external f: t = "f"`. */
export function typeOfDeclaration(text) {
  const declaration = /^(?:@[\w.]+(?:\([^)]*\))?\s+)*(?:let|external)\s+\S+?:\s*([\s\S]*)$/.exec(text);
  if (!declaration) return null;
  return oneLine(declaration[1])
    .replace(/ = "[^"]*"$/, "")
    .replace(SCRATCH, "");
}

/** `text` up to the first `separator` that is not inside brackets. */
function upTo(text, separators) {
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    const char = text[i];
    if ("(<[{".includes(char)) depth += 1;
    else if (char === ">" && text[i - 1] === "=") continue;
    else if (")>]}".includes(char)) depth -= 1;
    else if (depth === 0 && separators.some((separator) => text.startsWith(separator, i))) return text.slice(0, i);
  }
  return text;
}

/** The name a type starts with: `array` of `array<int>`, `Map.t` of `Map.t<int, string>`. */
export function typeHead(type) {
  const text = type.trim();
  const head = /^[A-Za-z_][\w.']*/.exec(text);
  return head ? head[0] : null;
}

/** The type of the first parameter of a function type, or null. */
export function firstParameter(type) {
  const text = type.trim();
  if (!text.includes("=>")) return null;
  let first;
  if (text.startsWith("(")) {
    // `(a, b) => c`, unless the brackets are a tuple that is the only parameter.
    let depth = 0;
    let end = -1;
    for (let i = 0; i < text.length; i++) {
      if ("(<[{".includes(text[i])) depth += 1;
      else if (text[i] === ">" && text[i - 1] === "=") continue;
      else if (")>]}".includes(text[i])) {
        depth -= 1;
        if (depth === 0) {
          end = i;
          break;
        }
      }
    }
    if (end < 0) return null;
    first = upTo(text.slice(1, end), [","]);
  } else {
    first = upTo(text, [" =>"]);
  }
  first = first.trim();
  // A labelled parameter is not what a pipe fills.
  if (first.startsWith("~")) return null;
  return first;
}

// The module with the functions of a type the compiler has built in.
const TYPE_MODULES = {
  array: "Array", string: "String", int: "Int", float: "Float", bool: "Bool", bigint: "BigInt", option: "Option",
  result: "Result", list: "List", dict: "Dict", promise: "Promise", exn: "Exn",
};

function isName(name) {
  return /^[A-Za-z_][A-Za-z0-9_']*$/.test(name);
}

function optionOf(item, extra = {}) {
  const collapsed = oneLine(item.text).replace(SCRATCH, "");
  let type = "variable";
  let detail = "";
  if (item.kind === "value") {
    detail = typeOfDeclaration(item.text) ?? "";
    if (item.shape?.k === "fn") type = "function";
  } else if (item.kind === "type") {
    type = "type";
    detail = collapsed.replace(/^(?:@[\w.]+(?:\([^)]*\))?\s+)*type\s+(?:rec\s+)?/, "");
  } else if (item.kind === "module") {
    type = "namespace";
    detail = "module";
  } else if (item.kind === "moduleType") {
    type = "interface";
    detail = "module type";
  } else if (item.kind === "exception") {
    type = "class";
    detail = collapsed.replace(/^type exn \+=\s*/, "exception ");
  }
  if (detail.length > 120) detail = `${detail.slice(0, 117)}…`;
  return { label: item.name, type, detail, ...extra };
}

export class CompilerCrash extends Error {}

/**
 * @param wasm  the initialized wasm-bindgen module of playground/crate
 */
export function createCompleter(wasm) {
  const PROBE = "Complete__P";
  // The file up to the item being written is a module that probes open. It
  // has a new name every time it changes: the compiler keeps what it knows
  // of an opened module by its name.
  let heads = 0;
  // The standard library does not change: what it gives every file.
  let globals = null;
  let cacheKey = null;
  let members = new Map();
  let head = null; // {text, name, module, items, opens}

  function dropHead() {
    if (head) wasm.forget_module(head.name);
    head = null;
    members = new Map();
  }

  function compile(text, name, opens) {
    try {
      return JSON.parse(wasm.compile_input(text, `${name}.res`, opens));
    } catch (error) {
      // A panic in the compiler: the wasm instance is unusable from here.
      throw new CompilerCrash(`The compiler crashed: ${String(error?.message ?? error)}`);
    }
  }

  function probe(text, opens) {
    const result = compile(text, PROBE, opens);
    wasm.forget_module(PROBE);
    return result;
  }

  function itemsOf(result) {
    return result.type === "success" ? (result.signature?.items ?? []) : null;
  }

  /** What `env` gives a probe: the modules it opens, and the `open`s of the file. */
  function scopeOf(env) {
    return {
      opens: head?.module ? [...env.opens, head.module] : env.opens,
      text: head && head.opens.length > 0 ? `${head.opens.join("\n")}\n` : "",
    };
  }

  /** The items of the module `path`, or null when there is no such module. */
  function membersOf(path, env) {
    const scope = scopeOf(env);
    const key = `${path}\n${scope.opens.join(",")}\n${scope.text}`;
    if (!members.has(key)) members.set(key, itemsOf(probe(`${scope.text}include ${path}`, scope.opens)));
    return members.get(key);
  }

  /** Compile the file up to the item being written, for what it defines. */
  function readHead(text, env) {
    if (head ? head.text === text : text.trim() === "") return;
    dropHead();
    if (text.trim() === "") return;
    heads += 1;
    const name = `Complete__H${heads}`;
    const prepared = JSON.parse(wasm.prepare_input(text, `${name}.res`));
    const opens = prepared.type === "success" ? prepared.opens : [];
    const result = compile(text, name, env.opens);
    head = {
      text,
      name,
      opens,
      module: result.type === "success" ? name : null,
      items: itemsOf(result) ?? [],
    };
  }

  /**
   * The type of the expression `at.operand`: in its place, then alone, for
   * when the item around it does not compile.
   */
  function typeOfOperand(at, source, env) {
    const scope = scopeOf(env);
    const operand = source.slice(at.operand.s, at.operand.e);
    const item = `${source.slice(at.start, at.operand.s)}(${operand}: complete__)${at.closers}`;
    const placed = probe(`${scope.text}type complete__\n${item}`, scope.opens);
    if (placed.type === "error") {
      const said = /This has type: ([\s\S]*?)\n\s*But [^\n]*\bcomplete__/.exec(stripAnsi(placed.message ?? ""));
      if (said) return oneLine(said[1]);
    }
    const alone = itemsOf(probe(`${scope.text}let it = (${operand})`, scope.opens));
    const it = alone?.find((candidate) => candidate.name === "it");
    return it ? typeOfDeclaration(it.text) : null;
  }

  /** The fields of the record type `type`, each with its type. */
  function fields(type, env) {
    const scope = scopeOf(env);
    const declaration = `${scope.text}external complete__v: ${type} = "v"\n`;
    const described = probe(declaration, scope.opens);
    if (described.type !== "success") return null;
    const shape = described.signature?.items?.find((item) => item.name === "complete__v")?.shape;
    const record = shape?.k === "ref" ? described.signature.defs[shape.id] : null;
    if (record?.k !== "record") return null;
    const names = record.fields.map((field) => field.name);
    const typed = itemsOf(
      probe(declaration + names.map((name, index) => `let f${index} = complete__v.${name}`).join("\n"), scope.opens),
    );
    return names.map((name, index) => ({
      label: name,
      type: "property",
      // In the order of the declaration.
      boost: 1 - index / names.length,
      detail: typeOfDeclaration(typed?.find((item) => item.name === `f${index}`)?.text ?? "") ?? "",
    }));
  }

  /**
   * The names a file can use without a module path. `own` leaves out what
   * every file has: the keywords and the standard library.
   */
  function names(env, statement, own = false) {
    if (!globals) {
      globals = [...(itemsOf(probe("include Pervasives", [])) ?? []), ...(itemsOf(probe("include Stdlib", [])) ?? [])];
    }
    const found = new Map();
    const add = (option) => {
      if (isName(option.label)) found.set(option.label, option);
    };
    if (!own) {
      for (const keyword of KEYWORDS) add({ label: keyword, type: "keyword", boost: -2 });
      // Names of the item being written: parameters, local bindings.
      for (const token of tokenize(statement).tokens) {
        if (token.t === "id" && !KEYWORD_SET.has(token.v)) add({ label: token.v, type: "text", boost: -1 });
      }
      for (const item of globals) add(optionOf(item));
    }
    for (const name of ["Macro", ...env.modules]) add({ label: name, type: "namespace", detail: "module" });
    const opened = [...env.opened, ...(head?.opens ?? []).map((open) => open.replace(/^open!?\s*/, "").trim())];
    for (const path of opened) for (const item of membersOf(path, env) ?? []) add(optionOf(item, { boost: 1 }));
    for (const item of env.scope) add(optionOf(item, { boost: 2 }));
    for (const item of head?.items ?? []) add(optionOf(item, { boost: 2 }));
    return [...found.values()];
  }

  /** Functions that take a `type` first: what can follow `value->`. */
  function pipes(type, env, statement) {
    const headName = typeHead(type);
    if (!headName) return null;
    const clean = headName.replace(SCRATCH, "");
    const dot = clean.lastIndexOf(".");
    const module = dot > 0 ? clean.slice(0, dot) : TYPE_MODULES[clean];
    const takes = (item, accepted) => {
      const signature = item.kind === "value" ? typeOfDeclaration(item.text) : null;
      const first = signature && firstParameter(signature);
      const firstHead = first && typeHead(first);
      // A type variable takes anything, which says nothing about this type.
      return firstHead ? accepted.includes(firstHead) : false;
    };
    const options = [];
    if (module) {
      const accepted = [clean, dot > 0 ? clean.slice(dot + 1) : "t"];
      for (const item of membersOf(module, env) ?? []) {
        if (isName(item.name) && takes(item, accepted)) options.push(optionOf(item, { label: `${module}.${item.name}` }));
      }
    }
    for (const option of names(env, statement)) {
      if (option.type !== "function") continue;
      const first = firstParameter(option.detail ?? "");
      if (first && typeHead(first) === clean) options.push({ ...option, boost: 3 });
    }
    return options;
  }

  /**
   * The completions at `offset` of `source`: `{from, options, validFor}`
   * with `options` of `{label, type, detail, boost}`, or null.
   *
   * @param env  `{key, opens, opened, modules, scope}`: what identifies the
   *   state of the project; the modules every file of it has open; the
   *   module paths that are open besides those; the names of its modules;
   *   and the items that are in scope without a path.
   */
  function complete(env, source, offset, explicit) {
    const at = contextAt(source, offset);
    if (!at) return null;
    if (cacheKey !== env.key) {
      cacheKey = env.key;
      dropHead();
    }
    readHead(source.slice(0, at.start), env);
    const statement = source.slice(at.start, at.from);
    const word = "^[A-Za-z0-9_']*$";
    const answer = (options, validFor = word) =>
      options && options.length > 0 ? { from: at.from, options, validFor } : null;

    if (at.kind === "member") {
      let items = membersOf(at.path, env);
      if (!items) return null;
      // After `%` and `@` only what a macro returns: code, a type, a pattern, declarations.
      if (at.sigil) items = items.filter((item) => item.kind === "module" || /\bMacro\.|\b(?:code|typ|pat|decls)\b/.test(item.text));
      return answer(items.filter((item) => isName(item.name)).map((item) => optionOf(item)));
    }
    if (at.kind === "sigil") {
      const forms =
        at.sigil === "%"
          ? [["code", "a quoted expression"], ["type", "a quoted type"], ["pat", "a quoted pattern"], ["Macro.eval", "the value of an expression, computed while compiling"], ["raw", "JavaScript"], ["re", "a regular expression"]]
          : [["macro", "the function is a macro"], ["generic", "a macro that is called like a function"], ["as", ""], ["unboxed", ""], ["deprecated", ""], ["module", ""], ["val", ""], ["send", ""], ["new", ""], ["get", ""], ["set", ""], ["scope", ""], ["variadic", ""], ["tag", ""], ["inline", ""], ["warning", ""]];
      // Macros are in the modules of the project, not in the standard library.
      const modules = names(env, statement, true).filter((option) => option.type === "namespace" && option.label !== "Macro");
      return answer(
        [...forms.map(([label, detail]) => ({ label, type: "keyword", detail, boost: 1 })), ...modules],
        "^[A-Za-z0-9_'.]*$",
      );
    }
    if (at.kind === "field" || at.kind === "pipe") {
      const type = typeOfOperand(at, source, env);
      if (!type) return null;
      return at.kind === "field" ? answer(fields(type, env)) : answer(pipes(type, env, statement), "^[A-Za-z0-9_'.]*$");
    }
    if (at.partial === "" && !explicit) return null;
    return answer(names(env, statement));
  }

  return { complete };
}
