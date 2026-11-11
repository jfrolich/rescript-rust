// The part of the macro engine that runs inside the JavaScript engine: a
// CommonJS-style loader for compiled ReScript modules and the entry point the
// compiler calls. It is the same script in the embedded QuickJS and in a
// browser. The embedder provides `__rescript_macro_source(moduleName)`, which
// returns the compiled JavaScript of a module or undefined.
//
// Macro code sees no clock, no random numbers and no network: a macro gets
// its inputs from the compiler (`readFile`, `env`, `Type.info`), which is
// what makes an expansion a function of recorded inputs.
//
// A macro cannot call back into the compiler. When it needs an answer the
// compiler has not given yet (the shape of a type, the text of a file), `ask`
// throws, the call returns `{need: question}`, and the compiler runs the macro
// again with the answer added. Macros are deterministic, so the second run
// takes the same path.
(function () {
  "use strict";
  var modules = Object.create(null);
  var state = { answers: Object.create(null), expected: null };

  globalThis.__rescript_macro = {
    ask: function (question) {
      if (Object.prototype.hasOwnProperty.call(state.answers, question)) {
        var answer = state.answers[question];
        if (answer !== null && typeof answer === "object" && typeof answer.__error === "string") {
          throw { __macro_error: answer.__error };
        }
        return answer === null ? undefined : answer;
      }
      throw { __macro_need: question };
    },
    fail: function (message, offset) {
      throw { __macro_error: String(message), offset: offset };
    },
    expected: function () {
      return state.expected;
    },
    // For embedders that also run compiled modules themselves.
    toCommonJs: function (source) {
      return toCommonJs(source);
    },
  };

  function moduleName(specifier) {
    var base = specifier.slice(specifier.lastIndexOf("/") + 1);
    var dot = base.indexOf(".");
    return dot < 0 ? base : base.slice(0, dot);
  }

  // The ES module output of the ReScript compiler has a fixed shape: imports
  // first, one export list last.
  function toCommonJs(source) {
    if (!/^\s*(import|export)\s/m.test(source)) return source;
    return source
      .replace(/^import \* as (\S+) from (["'][^"']+["']);?$/gm, "const $1 = require($2);")
      .replace(/^import (\{[^}]*\}) from (["'][^"']+["']);?$/gm, function (_, names, from) {
        return "const " + names.replace(/ as /g, ": ") + " = require(" + from + ");";
      })
      .replace(/^import (\S+) from (["'][^"']+["']);?$/gm, "const $1 = require($2).default;")
      .replace(/^export default (\S+?);?$/gm, "exports.default = $1;")
      .replace(/^export \{([^}]*)\};?$/gm, function (_, names) {
        return names
          .split(",")
          .map(function (entry) {
            var parts = entry.trim().split(/\s+as\s+/);
            if (parts[0] === "") return "";
            return "exports." + (parts[1] || parts[0]) + " = " + parts[0] + ";";
          })
          .join("\n");
      });
  }

  function refuse(what) {
    return function () {
      throw { __macro_error: what + " is not available at compile time: a macro has to give the same result every time." };
    };
  }

  // What a module of macro code sees in place of the globals of the same
  // name. The names of the browser's and Node's input and output are
  // undefined.
  var hidden = [
    "fetch", "XMLHttpRequest", "WebSocket", "importScripts", "postMessage", "navigator", "location",
    "indexedDB", "caches", "localStorage", "sessionStorage", "document", "window", "self", "process",
    "setTimeout", "setInterval", "setImmediate", "queueMicrotask", "performance", "crypto",
  ];
  var sandbox = (function () {
    var math = Object.create(Math);
    math.random = refuse("Math.random");
    var RealDate = Date;
    function FixedDate() {
      if (arguments.length === 0) refuse("The current time")();
      return new (Function.prototype.bind.apply(RealDate, [null].concat(Array.prototype.slice.call(arguments))))();
    }
    FixedDate.prototype = RealDate.prototype;
    FixedDate.UTC = RealDate.UTC;
    FixedDate.parse = RealDate.parse;
    FixedDate.now = refuse("Date.now");
    return { Math: math, Date: FixedDate };
  })();

  function run(source, module) {
    var parameters = ["require", "exports", "module", "Math", "Date"].concat(hidden);
    Function.apply(null, parameters.concat([toCommonJs(source)]))(
      function (specifier) {
        return load(moduleName(specifier));
      },
      module.exports,
      module,
      sandbox.Math,
      sandbox.Date,
    );
  }

  function load(name) {
    var loaded = modules[name];
    if (loaded) return loaded.exports;
    var source = __rescript_macro_source(name);
    if (source === undefined || source === null) {
      throw { __macro_error: "Macro code needs the module `" + name + "`, which is not available at compile time." };
    }
    var module = { exports: {} };
    modules[name] = module;
    try {
      run(source, module);
    } catch (error) {
      delete modules[name];
      throw error;
    }
    return module.exports;
  }

  // The source text of a compile-time value, read by its type.
  function reify(value, shape) {
    switch (shape.k) {
      case "int":
        return String(value | 0);
      case "float":
        if (!isFinite(value)) throw { __macro_error: "%comptime: the value is not a finite number." };
        return /[.e]/.test(String(value)) ? String(value) : String(value) + ".";
      case "string":
        return JSON.stringify(String(value));
      case "bool":
        return value ? "true" : "false";
      case "unit":
        return "()";
      case "array":
        return "[" + value.map(function (item) { return reify(item, shape.of); }).join(", ") + "]";
      case "tuple":
        return "(" + shape.of.map(function (item, index) { return reify(value[index], item); }).join(", ") + ")";
      case "option":
        if (value === undefined) return "None";
        if (value !== null && typeof value === "object" && value.BS_PRIVATE_NESTED_SOME_NONE !== undefined) {
          throw { __macro_error: "%comptime: a nested option cannot be written as a literal." };
        }
        return "Some(" + reify(value, shape.of) + ")";
      case "dict":
        return "dict{" + Object.keys(value).map(function (key) {
          return JSON.stringify(key) + ": " + reify(value[key], shape.of);
        }).join(", ") + "}";
      case "record":
        return "{" + shape.fields.map(function (field) {
          var item = value[field.js];
          if (field.optional) return item === undefined ? null : field.name + ": " + reify(item, field.of);
          return field.name + ": " + reify(item, field.of);
        }).filter(function (item) { return item !== null; }).join(", ") + "}";
      default:
        throw { __macro_error: "%comptime: a value of type " + shape.name + " cannot be written as a literal." };
    }
  }

  function describe(error) {
    if (error && typeof error === "object") {
      if (error.RE_EXN_ID !== undefined) {
        var parts = [String(error.RE_EXN_ID)];
        if (error._1 !== undefined) parts.push(typeof error._1 === "string" ? error._1 : JSON.stringify(error._1));
        if (error.Error && error.Error.message) parts.push(error.Error.message);
        return parts.join(": ");
      }
      if (error.message !== undefined) return String(error.message);
    }
    return String(error);
  }

  globalThis.__rescript_macro_call = function (requestJson) {
    var request = JSON.parse(requestJson);
    state.answers = request.answers || Object.create(null);
    state.expected = request.expected || null;
    try {
      if (request.kind === "reset") {
        modules = Object.create(null);
        return JSON.stringify({ ok: "" });
      }
      if (request.kind === "eval") {
        // %comptime: `source` is a compiled module that exports `value`.
        var module = { exports: {} };
        run(request.source, module);
        return JSON.stringify({ ok: reify(module.exports.value, request.shape) });
      }
      // `name` is a path in the module's exports: `Inner.encode` is a macro
      // in a submodule.
      var macro = request.name.split(".").reduce(function (value, key) {
        return value === null || value === undefined ? undefined : value[key];
      }, load(request.module));
      if (typeof macro !== "function") {
        throw { __macro_error: "`" + request.module + "." + request.name + "` is not a function, so it cannot run as a macro." };
      }
      var result = macro.apply(null, request.args);
      if (result === null || typeof result !== "object" || typeof result.c !== "string") {
        throw { __macro_error: "The macro `" + request.module + "." + request.name + "` did not return code." };
      }
      return JSON.stringify({ ok: result.c });
    } catch (error) {
      if (error && error.__macro_need !== undefined) return JSON.stringify({ need: error.__macro_need });
      if (error && error.__macro_error !== undefined) {
        return JSON.stringify({ error: error.__macro_error, offset: error.offset === undefined ? null : error.offset });
      }
      return JSON.stringify({ error: "The macro raised an exception: " + describe(error) });
    }
  };
})();
