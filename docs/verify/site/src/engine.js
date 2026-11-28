/**
 * The compiler module (crate/) behind one function: `build(file)`.
 *
 * The module is built for WASI. It needs a handful of WASI calls and no file
 * system: the file of an example comes in with each request. This is used by
 * the page's worker and by the script that builds the examples with the page.
 */

const encoder = new TextEncoder();
const decoder = new TextDecoder();

/** The WASI calls the module imports. `stderr` receives what it prints. */
function wasi(memory, stderr) {
  const view = () => new DataView(memory().buffer);
  const bytes = () => new Uint8Array(memory().buffer);
  const BADF = 8;
  const NOENT = 44;
  return {
    random_get(pointer, length) {
      const target = bytes().subarray(pointer, pointer + length);
      // getRandomValues refuses a view of shared or growable memory in some
      // engines, so fill a copy.
      const random = new Uint8Array(length);
      globalThis.crypto.getRandomValues(random);
      target.set(random);
      return 0;
    },
    environ_sizes_get(count, size) {
      view().setUint32(count, 0, true);
      view().setUint32(size, 0, true);
      return 0;
    },
    environ_get: () => 0,
    clock_time_get(_id, _precision, result) {
      view().setBigUint64(result, BigInt(Math.round(performance.now() * 1e6)), true);
      return 0;
    },
    fd_write(fd, iovs, count, written) {
      let total = 0;
      let text = "";
      for (let index = 0; index < count; index++) {
        const pointer = view().getUint32(iovs + index * 8, true);
        const length = view().getUint32(iovs + index * 8 + 4, true);
        text += decoder.decode(bytes().slice(pointer, pointer + length));
        total += length;
      }
      if (fd === 1 || fd === 2) stderr(text);
      view().setUint32(written, total, true);
      return 0;
    },
    fd_close: () => 0,
    fd_read: () => BADF,
    fd_fdstat_get: () => BADF,
    fd_filestat_get: () => BADF,
    fd_prestat_get: () => BADF,
    fd_prestat_dir_name: () => BADF,
    path_open: () => NOENT,
    sched_yield: () => 0,
    proc_exit(code) {
      throw new Error(`the compiler exited with status ${code}`);
    },
  };
}

/**
 * `module` is the compiled WebAssembly module, `stdlib` the runtime sources
 * by path. A build that crashes leaves the instance unusable: `build` then
 * returns `{crashed}` and the caller makes a new engine.
 */
export function createEngine(module, stdlib) {
  let instance = null;
  let printed = "";

  function call(request) {
    const exports = instance.exports;
    const input = encoder.encode(JSON.stringify(request));
    const pointer = exports.rv_input(input.length);
    new Uint8Array(exports.memory.buffer, pointer, input.length).set(input);
    exports.rv_run();
    const output = new Uint8Array(exports.memory.buffer, exports.rv_output(), exports.rv_output_len());
    return JSON.parse(decoder.decode(output.slice()));
  }

  function start() {
    printed = "";
    const calls = wasi(
      () => instance.exports.memory,
      (text) => {
        printed += text;
      },
    );
    // The module links the file-system calls too, for code paths the page
    // never takes. Any call not provided above answers "not supported".
    const NOSYS = 52;
    const imports = {};
    for (const { module: from, name } of WebAssembly.Module.imports(module)) {
      (imports[from] ??= {})[name] = calls[name] ?? (() => NOSYS);
    }
    instance = new WebAssembly.Instance(module, imports);
    // A WASI library module: `_initialize` runs its constructors.
    instance.exports._initialize?.();
    call({ op: "stdlib", files: stdlib });
  }

  start();

  return {
    /** `file` is `{name, source}`: one ReScript file. */
    build(file) {
      printed = "";
      try {
        const result = call({ op: "build", name: file.name, source: file.source });
        const warnings = [result.warnings, printed.trim()].filter(Boolean).join("\n");
        return { ...result, warnings };
      } catch (error) {
        const message = printed.trim() || String(error?.message ?? error);
        try {
          start();
        } catch {
          return { crashed: message };
        }
        return { type: "error", message: `The compiler stopped:\n${message}`, warnings: "" };
      }
    },
    memory: () => instance.exports.memory.buffer.byteLength,
  };
}
