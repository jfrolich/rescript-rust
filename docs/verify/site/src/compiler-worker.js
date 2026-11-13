/**
 * The compiler, in a worker, so that compiling never blocks the page and a
 * build that hangs can be stopped (see compiler.js).
 */
import { createEngine } from "./engine.js";

let engine = null;

self.onmessage = async (event) => {
  const message = event.data;
  try {
    if (message.type === "init") {
      const [module, stdlib] = await Promise.all([
        WebAssembly.compileStreaming(fetch(message.wasmUrl)),
        fetch(message.stdlibUrl).then((response) => {
          if (!response.ok) throw new Error(`cannot load the standard library (${response.status})`);
          return response.json();
        }),
      ]);
      engine = createEngine(module, stdlib);
      self.postMessage({ type: "ready" });
    } else if (message.type === "build") {
      const started = performance.now();
      const result = engine.build(message.file);
      self.postMessage({ type: "built", id: message.id, result, ms: performance.now() - started });
    }
  } catch (error) {
    self.postMessage({ type: "failed", id: message.id, message: String(error?.message ?? error) });
  }
};
