/**
 * The compiler, in a worker: a macro that does not terminate hangs this
 * thread, not the page, and the page can stop it (see compiler-client.js).
 */
import init, * as wasm from "../crate/pkg/rescript_playground_wasm.js";
import { createEngine } from "./engine.js";

let engine = null;

self.onmessage = async (event) => {
  const message = event.data;
  try {
    if (message.type === "init") {
      await init();
      const response = await fetch(message.stdlibUrl);
      if (!response.ok) throw new Error(`cannot load the standard library (${response.status})`);
      engine = createEngine(wasm, await response.json());
      self.postMessage({ type: "ready" });
    } else if (message.type === "build") {
      const started = performance.now();
      const result = engine.build(message.files);
      self.postMessage({ type: "built", id: message.id, result, ms: performance.now() - started });
    }
  } catch (error) {
    self.postMessage({ type: "failed", id: message.id, message: String(error?.message ?? error) });
  }
};
