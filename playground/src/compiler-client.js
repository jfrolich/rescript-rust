/**
 * The page's side of the compiler worker. Builds are requested one at a
 * time; while one runs, only the latest request waits. A build that takes
 * longer than `TIME_LIMIT` is stopped by replacing the worker.
 */

const TIME_LIMIT = 20_000;

export function createCompiler({ onReady, onResult, onFailure }) {
  let worker = null;
  let ready = false;
  let running = null; // {id, timer}
  let waiting = null; // files
  let nextId = 1;

  function start() {
    ready = false;
    worker = new Worker(new URL("./compiler-worker.js", import.meta.url), { type: "module" });
    worker.onmessage = (event) => {
      const message = event.data;
      if (message.type === "ready") {
        ready = true;
        onReady();
        next();
      } else if (message.type === "built") {
        if (!running || running.id !== message.id) return;
        clearTimeout(running.timer);
        running = null;
        if (message.result.crashed) {
          // The compiler panicked: its memory is in an unknown state.
          restart();
          onFailure(message.result.crashed);
        } else {
          onResult(message.result, message.ms);
        }
        next();
      } else if (message.type === "failed") {
        if (running) clearTimeout(running.timer);
        running = null;
        restart();
        onFailure(`The compiler failed: ${message.message}`);
      }
    };
    worker.onerror = (event) => {
      if (running) clearTimeout(running.timer);
      running = null;
      onFailure(`The compiler failed: ${event.message || "unknown error"}`);
    };
    worker.postMessage({ type: "init", stdlibUrl: new URL("stdlib.json", document.baseURI).href });
  }

  function restart() {
    worker.terminate();
    start();
  }

  function next() {
    if (!ready || running || !waiting) return;
    const files = waiting;
    waiting = null;
    const id = nextId++;
    const timer = setTimeout(() => {
      running = null;
      restart();
      onFailure(
        `The build was stopped after ${TIME_LIMIT / 1000} seconds. A macro or the program probably does not terminate.`,
      );
    }, TIME_LIMIT);
    running = { id, timer };
    worker.postMessage({ type: "build", id, files });
  }

  start();

  return {
    build(files) {
      waiting = files;
      next();
    },
    dispose() {
      if (running) clearTimeout(running.timer);
      worker.terminate();
    },
  };
}
