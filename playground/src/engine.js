/**
 * The playground's build: compiles the files of a small project in
 * dependency order with the compiler in WebAssembly, runs macros in this
 * JavaScript engine, and runs the compiled program.
 *
 * It has no dependency on the page, so the same code runs in the worker and
 * in the Node smoke test (scripts/smoke.mjs).
 */

import { CompilerCrash, createCompleter } from "./complete.js";
import { formatException, formatValue, hideModules } from "./repl-format.js";

export function moduleNameOf(filename) {
  const base = filename.split("/").pop();
  const dot = base.lastIndexOf(".");
  const name = dot < 0 ? base : base.slice(0, dot);
  return name.charAt(0).toUpperCase() + name.slice(1);
}

export function isSourceFile(filename) {
  return filename.endsWith(".res");
}

/**
 * The source files in the order they have to be compiled: a file after the
 * files it mentions. Returns `{order, dependencies, cycle}`.
 */
export function compileOrder(files) {
  const sources = files.filter((file) => isSourceFile(file.name));
  const names = sources.map((file) => moduleNameOf(file.name));
  const dependencies = new Map();
  sources.forEach((file, index) => {
    const found = [];
    names.forEach((name, other) => {
      if (other === index) return;
      // The module name where no longer name contains it: `Json.encode`,
      // `%Json.codec`, `open Json`.
      const mention = new RegExp(`(^|[^A-Za-z0-9_'.])${name}(?![A-Za-z0-9_'])`);
      if (mention.test(file.source)) found.push(sources[other].name);
    });
    dependencies.set(file.name, found);
  });

  const order = [];
  const state = new Map();
  let cycle = null;
  const visit = (name, path) => {
    if (state.get(name) === "done") return;
    if (state.get(name) === "open") {
      cycle = cycle || path.slice(path.indexOf(name)).concat(name);
      return;
    }
    state.set(name, "open");
    for (const dependency of dependencies.get(name)) visit(dependency, path.concat(name));
    state.set(name, "done");
    order.push(name);
  };
  for (const file of sources) visit(file.name, []);
  return { order, dependencies, cycle };
}

function stripAnsi(text) {
  return text.replace(/\u001b\[[0-9;]*m/g, "");
}

function show(value, depth = 0) {
  if (typeof value === "string") return depth === 0 ? value : JSON.stringify(value);
  if (value === undefined) return "undefined";
  if (typeof value === "function") return "[function]";
  if (typeof value === "bigint") return `${value}n`;
  if (typeof value === "symbol") return value.toString();
  if (value instanceof Error) return `${value.name}: ${value.message}`;
  if (value === null || typeof value !== "object") return String(value);
  if (depth > 6) return "…";
  if (Array.isArray(value)) return `[${value.map((item) => show(item, depth + 1)).join(", ")}]`;
  const entries = Object.keys(value).map((key) => `${key}: ${show(value[key], depth + 1)}`);
  return entries.length === 0 ? "{}" : `{${entries.join(", ")}}`;
}

/**
 * @param wasm    the initialized wasm-bindgen module of playground/crate
 * @param stdlib  `{sources, javascript}` of public/stdlib.json
 */
export function createEngine(wasm, stdlib) {
  // The standard library: sources for the type checker, an interface before
  // its implementation.
  const stdlibModules = new Map();
  for (const [path, content] of Object.entries(stdlib.sources)) {
    wasm.vfs_write_file(path, content);
    const name = path.split("/").pop().replace(/\.resi?$/, "");
    if (!stdlibModules.has(name) || path.endsWith(".resi")) stdlibModules.set(name, path);
  }
  const registerStdlib = (name) => wasm.register_source_module(name, stdlibModules.get(name));
  for (const name of stdlibModules.keys()) registerStdlib(name);

  // Compiled JavaScript of the project, by module name.
  let projectJs = Object.create(null);
  let projectFiles = [];
  // Counts the builds: what a completion found is of one build.
  let projectVersion = 0;
  const javascriptOf = (name) => projectJs[name] ?? stdlib.javascript[name];

  // The macro engine is this JavaScript engine: host.js gets the compiled
  // modules from here, the compiler calls `__rescript_macro_call`.
  globalThis.__rescript_macro_source = javascriptOf;
  (0, eval)(wasm.macro_host_js());
  const macroCall = (request) => globalThis.__rescript_macro_call(JSON.stringify(request));
  const toCommonJs = globalThis.__rescript_macro.toCommonJs;

  function run(order) {
    const logs = [];
    const log = (level) => (...values) =>
      logs.push({ level, text: values.map((value) => show(value)).join(" ") });
    const console = { log: log("log"), info: log("log"), debug: log("log"), warn: log("warn"), error: log("error") };
    const loaded = Object.create(null);
    const load = (name) => {
      if (loaded[name]) return loaded[name].exports;
      const source = javascriptOf(name);
      if (source === undefined) throw new Error(`The module ${name} is not part of this playground.`);
      const module = { exports: {} };
      loaded[name] = module;
      new Function("require", "exports", "module", "console", toCommonJs(source))(
        (specifier) => load(moduleNameOf(specifier)),
        module.exports,
        module,
        console,
      );
      return module.exports;
    };
    try {
      for (const filename of order) load(moduleNameOf(filename));
    } catch (error) {
      logs.push({ level: "error", text: `Uncaught ${describeException(error)}` });
    }
    return logs;
  }

  function describeException(error) {
    if (error && typeof error === "object" && error.RE_EXN_ID !== undefined) {
      const parts = [String(error.RE_EXN_ID)];
      if (error._1 !== undefined) parts.push(show(error._1));
      return parts.join(": ");
    }
    return show(error);
  }

  /**
   * Compile `files` (`[{name, source}]`) and run the result.
   * Returns `{order, results, logs}`: per source file `{type: "success", js,
   * expanded, warnings, ...}`, `{type: "error", message}` or `{type:
   * "skipped", message}`; `logs` is null when a file did not compile.
   */
  function build(files, { execute = true } = {}) {
    // Start from nothing: a module of the previous build must not be visible.
    for (const file of projectFiles) {
      const name = moduleNameOf(file.name);
      if (isSourceFile(file.name)) {
        wasm.forget_module(name);
        if (stdlibModules.has(name)) registerStdlib(name);
      } else {
        wasm.vfs_delete_file(`/${file.name}`);
      }
    }
    projectFiles = files;
    projectVersion += 1;
    projectJs = Object.create(null);
    macroCall({ kind: "reset" });
    // Other files are what `Macro.readFile` reads.
    for (const file of files) {
      if (!isSourceFile(file.name)) wasm.vfs_write_file(`/${file.name}`, file.source);
    }

    const { order, dependencies, cycle } = compileOrder(files);
    const results = {};
    if (cycle) {
      const message = `These files depend on each other in a cycle: ${cycle.join(" → ")}`;
      for (const name of order) results[name] = { type: "error", message };
      return { order, results, logs: null };
    }
    let ok = true;
    for (const name of order) {
      const failed = dependencies.get(name).find((dependency) => results[dependency]?.type !== "success");
      if (failed) {
        results[name] = { type: "skipped", message: `Not compiled: it depends on ${failed}, which has an error.` };
        ok = false;
        continue;
      }
      const file = files.find((candidate) => candidate.name === name);
      const started = performance.now();
      let result;
      try {
        result = JSON.parse(wasm.compile_file(file.source, file.name, false));
      } catch (error) {
        // A panic in the compiler: the wasm instance is unusable from here.
        return { order, results, logs: null, crashed: `The compiler crashed on ${name}: ${show(error)}` };
      }
      result.ms = performance.now() - started;
      if (result.type === "success") {
        projectJs[moduleNameOf(name)] = result.js;
        result.warnings = stripAnsi(result.warnings || "").trim();
      } else {
        result.message = stripAnsi(result.message || "").trim();
        ok = false;
      }
      results[name] = result;
    }
    return { order, results, logs: ok && execute ? run(order) : null };
  }

  // ── The read-eval-print loop ──────────────────────────────────────────────
  //
  // An input is compiled as a file of its own, `Repl<n>.res`, with the files
  // of the earlier inputs opened, and its JavaScript is run once: what an
  // input defined, and what it did, stays.

  let session = null;
  // Counts the inputs of every session: the compiler keeps what it knows of
  // an opened module by its name, so a name is not used a second time.
  let inputs = 0;
  const asyncFunction = Object.getPrototypeOf(async () => {}).constructor;
  const inputModules = /\bRepl\d+(_open\d+)?\./g;
  const hideInputModules = (text) => text.replace(inputModules, "");
  hideModules(inputModules);

  /** End the session: its inputs are gone. */
  function replEnd() {
    for (const name of session?.files ?? []) wasm.forget_module(name);
    session = null;
  }

  /**
   * Start a session with the modules of `libraries` (`[{name, source}]`)
   * available. `onLog` gets what the program prints after its input has
   * finished (a timer, a promise). Returns `{modules, problems}`.
   */
  function replStart(libraries, onLog = () => {}) {
    replEnd();
    const { order, results } = build(libraries, { execute: false });
    session = {
      // The modules the inputs were compiled as.
      files: [],
      // What the inputs defined, by name: the names an input can use.
      scope: new Map(),
      // What every input opens: earlier inputs, and the modules they opened.
      opens: [],
      // The modules an input defined: `open` of one is not `open` of a file.
      defined: new Set(),
      loaded: Object.create(null),
      // The output of the input that is running, or null between inputs.
      printing: null,
    };
    // One console for the whole session: a function prints where it is
    // called, which is not always the input that defined it. Between inputs
    // (a timer, a promise) the line goes to `onLog`.
    const current = session;
    const log = (kind) => (...values) => {
      const line = { kind, text: values.map((value) => show(value)).join(" ") };
      if (current.printing) current.printing.push(line);
      else onLog(line);
    };
    session.console = { log: log("log"), info: log("log"), debug: log("log"), warn: log("warn"), error: log("error") };
    return {
      modules: order.filter((name) => results[name].type === "success").map(moduleNameOf),
      problems: order
        .filter((name) => results[name].type !== "success")
        .map((name) => ({ file: name, message: results[name].message })),
    };
  }

  function replLoad(name) {
    const { loaded, console } = session;
    if (loaded[name]) return loaded[name].exports;
    const source = javascriptOf(name);
    if (source === undefined) throw new Error(`The module ${name} is not part of this session.`);
    const module = { exports: {} };
    loaded[name] = module;
    try {
      new Function("require", "exports", "module", "console", toCommonJs(source))(
        (specifier) => replLoad(moduleNameOf(specifier)),
        module.exports,
        module,
        console,
      );
    } catch (error) {
      delete loaded[name];
      throw error;
    }
    return module.exports;
  }

  /**
   * A diagnostic of an input as the input was written: without the name of
   * its file, and without the binding of its last expression (`prepared`,
   * of `prepare_input`), which moved what is after it on that line.
   */
  function replDiagnostic(message, filename, prepared) {
    const [line, column] = prepared.result_at ?? [0, 0];
    const width = prepared.binding?.length ?? 0;
    const moved = (at, col) => (Number(at) === line && Number(col) >= column ? Math.max(column, Number(col) - width) : col);
    const escaped = filename.replace(/[.]/g, "\\.");
    let text = message.replace(
      new RegExp(`${escaped}:(\\d+):(\\d+)(?:-(\\d+)(?::(\\d+))?)?`, "g"),
      (_, startLine, startColumn, end, endColumn) => {
        let out = `${startLine}:${moved(startLine, startColumn)}`;
        // `l:c-c2` ends on the same line, `l:c-l2:c2` on another one.
        if (endColumn !== undefined) out += `-${end}:${moved(end, endColumn)}`;
        else if (end !== undefined) out += `-${moved(startLine, end)}`;
        return `input:${out}`;
      },
    );
    if (line > 0) {
      // The line of the binding in a frame of the source: `  2 │ let it = x`.
      text = text.replace(new RegExp(`^(\\s*${line} [│|] .{${column - 1}})${prepared.binding}`, "gm"), "$1");
    }
    return text;
  }

  /** Keep `open Path` of an input open for the inputs after it. */
  function replKeepOpen(text, input) {
    const path = text.replace(/^open!?\s*/, "").trim();
    const root = path.split(".")[0];
    const isFile = !session.defined.has(root) && (stdlibModules.has(root) || projectJs[root] !== undefined);
    if (isFile && path === root) {
      session.opens.push(path);
      return null;
    }
    // Anything else is opened by a file that includes it.
    const name = `${input}_open${session.opens.length}`;
    const result = JSON.parse(wasm.compile_input(`include ${path}`, `${name}.res`, session.opens));
    if (result.type !== "success") return `\`${text}\` is not kept open for the inputs after this one.`;
    projectJs[name] = result.js;
    session.files.push(name);
    replLoad(name);
    session.opens.push(name);
    return null;
  }

  /**
   * Compile and run one input. Returns `{output, expanded, javascript}`:
   * `output` is a list of `{kind, text}` with kind `value` (a definition,
   * with its value when it has one), `log`, `warn`, `error` (printed by the
   * program), `problem` (it does not compile, or it raised) or `note`.
   */
  async function replEval(source) {
    if (!session) replStart([]);
    const current = session;
    inputs += 1;
    const name = `Repl${inputs}`;
    current.files.push(name);
    const filename = `${name}.res`;
    const output = [];

    const prepared = JSON.parse(wasm.prepare_input(source, filename));
    const text = prepared.type === "success" ? prepared.source : source;
    let result;
    try {
      result = JSON.parse(wasm.compile_input(text, filename, current.opens));
    } catch (error) {
      // A panic in the compiler: the wasm instance is unusable from here.
      return { output, crashed: `The compiler crashed: ${show(error)}` };
    }
    const diagnostic = (message) =>
      replDiagnostic(stripAnsi(message || "").trim(), filename, prepared.type === "success" ? prepared : {});
    if (result.type !== "success") {
      output.push({ kind: "problem", text: diagnostic(result.message) });
      return { output };
    }
    projectJs[name] = result.js;

    const module = { exports: {} };
    // What is printed while the input runs is its output, whoever prints it.
    current.printing = output;
    try {
      // An input can `await` at the top level.
      await new asyncFunction("require", "exports", "module", "console", toCommonJs(result.js))(
        (specifier) => replLoad(moduleNameOf(specifier)),
        module.exports,
        module,
        current.console,
      );
    } catch (error) {
      current.printing = null;
      // What it defined before it raised is not kept: part of it is missing.
      wasm.forget_module(name);
      delete projectJs[name];
      output.push({ kind: "problem", text: `Uncaught ${formatException(error)}` });
      return { output, expanded: result.expanded ?? null, javascript: result.js };
    }
    current.printing = null;
    current.loaded[name] = module;
    current.opens.push(name);

    const warnings = diagnostic(result.warnings);
    if (warnings) output.push({ kind: "warn", text: warnings });
    const { items = [], defs = [] } = result.signature ?? {};
    for (const item of items) {
      const declaration = hideInputModules(item.text).replace(/^type exn \+=\s+/, "exception ");
      if (item.kind === "module") current.defined.add(item.name);
      current.scope.set(item.name, item);
      if (item.kind !== "value" || declaration.startsWith("external ") || !(item.name in module.exports)) {
        output.push({ kind: "value", text: declaration });
        continue;
      }
      // `let it: int` of an expression is written `- : int`.
      const head =
        item.name === "it" && prepared.result_at ? declaration.replace(/^let it: ?/, "- : ") : declaration;
      const last = head.split("\n").pop();
      const value = formatValue(module.exports[item.name], item.shape, defs, 0);
      // A value that does not fit after the type starts a line of its own.
      const joined =
        last.length + 3 + value.split("\n")[0].length <= 80 ? `${head} = ${value}` : `${head} =\n  ${formatValue(module.exports[item.name], item.shape, defs, 2)}`;
      output.push({ kind: "value", text: joined });
    }
    for (const open of prepared.opens ?? []) {
      const note = replKeepOpen(open, name);
      if (note) output.push({ kind: "note", text: note });
    }
    return { output, expanded: result.expanded ?? null, javascript: result.js };
  }

  /**
   * Type check the parts of the standard library most programs use, so
   * that the first real build does not wait for them.
   */
  function warm() {
    build([
      {
        name: "Warm.res",
        source:
          'let run = () => {\n' +
          '  Console.log([1]->Array.map(x => x + 1)->Array.join(","))\n' +
          '  let entries = Dict.fromArray([("a", JSON.Encode.string("b"))])\n' +
          '  JSON.stringify(JSON.Encode.object(entries))->String.length->Int.toString->Option.Some\n' +
          '}\n',
      },
    ]);
    build([]);
  }

  // ── Completion ────────────────────────────────────────────────────────────

  const completer = createCompleter(wasm);

  /**
   * What can be written at `offset`. In a session of the read-eval-print
   * loop (`{mode: "repl", source, offset}`) the input sees the inputs before
   * it; in a project (`{mode: "project", files, name, offset}`) the file
   * `name` sees the files it depends on, which are compiled if they are not.
   * Returns `{from, options, validFor}`, null, or `{crashed}`.
   */
  function complete(request) {
    try {
      if (request.mode === "repl") {
        if (!session) replStart([]);
        const inputs = /^Repl\d+$/;
        return completer.complete(
          {
            key: `repl/${projectVersion}/${session.opens.length}`,
            opens: session.opens,
            // What an `open` of an input opened.
            opened: session.opens.filter((name) => !inputs.test(name)),
            modules: projectFiles.filter((file) => isSourceFile(file.name)).map((file) => moduleNameOf(file.name)),
            scope: [...session.scope.values()],
          },
          request.source,
          request.offset,
          request.explicit,
        );
      }
      const { files, name } = request;
      const built =
        !session &&
        files.length === projectFiles.length &&
        files.every(
          (file, index) =>
            file.name === projectFiles[index].name && (file.name === name || file.source === projectFiles[index].source),
        );
      if (!built) {
        replEnd();
        const outcome = build(files, { execute: false });
        if (outcome.crashed) return { crashed: outcome.crashed };
      }
      const file = files.find((candidate) => candidate.name === name);
      if (!file || !isSourceFile(name)) return null;
      return completer.complete(
        {
          key: `project/${projectVersion}`,
          opens: [],
          opened: [],
          modules: files.filter((other) => isSourceFile(other.name) && other.name !== name).map((other) => moduleNameOf(other.name)),
          scope: [],
        },
        file.source,
        request.offset,
        request.explicit,
      );
    } catch (error) {
      if (error instanceof CompilerCrash) return { crashed: error.message };
      throw error;
    }
  }

  return { build, warm, replStart, replEval, complete };
}
