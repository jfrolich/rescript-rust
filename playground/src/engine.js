/**
 * The playground's build: compiles the files of a small project in
 * dependency order with the compiler in WebAssembly, runs macros in this
 * JavaScript engine, and runs the compiled program.
 *
 * It has no dependency on the page, so the same code runs in the worker and
 * in the Node smoke test (scripts/smoke.mjs).
 */

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
  function build(files) {
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
    return { order, results, logs: ok ? run(order) : null };
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

  return { build, warm };
}
