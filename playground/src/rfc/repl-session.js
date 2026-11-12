/**
 * The page's side of the read-eval-print loop: a compiler worker of its
 * own, so that what the loop has defined is not touched by the examples of
 * the page, and so that an input that does not end can be stopped without
 * stopping them.
 */

const TIME_LIMIT = 20_000;
const COMPLETION_LIMIT = 3_000;

/**
 * @param libraries  `[{name, source}]`: the modules the session starts with
 * @param replay     inputs that are evaluated before the first one of the reader
 * @param onLog      what the program prints after its input has finished
 * @param onStatus   `idle`, `loading`, `ready` or `failed`
 */
export function createSession({ libraries, replay, onLog, onStatus }) {
  let worker = null;
  let ready = null; // a promise, once the worker is started
  let nextId = 1;
  const pending = new Map(); // id -> {resolve, reject, timer}

  function settle(id, outcome, value) {
    const request = pending.get(id);
    if (!request) return;
    pending.delete(id);
    clearTimeout(request.timer);
    request[outcome](value);
  }

  function stop(message) {
    if (worker) worker.terminate();
    worker = null;
    ready = null;
    for (const id of [...pending.keys()]) settle(id, "reject", new Error(message));
    onStatus("idle");
  }

  function start() {
    if (ready) return ready;
    onStatus("loading");
    worker = new Worker(new URL("../compiler-worker.js", import.meta.url), { type: "module" });
    ready = new Promise((resolve, reject) => {
      worker.onmessage = (event) => {
        const message = event.data;
        if (message.type === "ready") {
          worker.postMessage({ type: "repl-start", libraries, replay });
        } else if (message.type === "repl-started") {
          onStatus("ready");
          resolve(message);
        } else if (message.type === "repl-result") {
          if (message.result.crashed) {
            stop(message.result.crashed);
          } else {
            settle(message.id, "resolve", { ...message.result, ms: message.ms });
          }
        } else if (message.type === "completed") {
          if (message.result?.crashed) {
            onLog({ kind: "problem", text: `${message.result.crashed}\nThe session starts again: what it had defined is gone.` });
            stop(message.result.crashed);
          } else {
            settle(message.id, "resolve", message.result);
          }
        } else if (message.type === "repl-log") {
          onLog(message.line);
        } else if (message.type === "failed") {
          const text = `The compiler failed: ${message.message}`;
          reject(new Error(text));
          stop(text);
          onStatus("failed");
        }
      };
      worker.onerror = (event) => {
        const text = `The compiler failed: ${event.message || "it could not be loaded"}`;
        reject(new Error(text));
        stop(text);
        onStatus("failed");
      };
    });
    // Nothing waits for a session that is only warming up.
    ready.catch(() => {});
    worker.postMessage({ type: "init", stdlibUrl: new URL("stdlib.json", document.baseURI).href });
    return ready;
  }

  return {
    /** Load the compiler and the session's modules, if they are not. */
    warmUp() {
      start();
    },
    /**
     * Evaluate one input. Resolves with `{output, expanded, javascript, ms}`;
     * rejects when the session had to be stopped, and is then a new one.
     */
    async evaluate(source) {
      await start();
      return new Promise((resolve, reject) => {
        const id = nextId++;
        const timer = setTimeout(() => {
          stop(`Stopped after ${TIME_LIMIT / 1000} seconds: the input probably does not end.`);
        }, TIME_LIMIT);
        pending.set(id, { resolve, reject, timer });
        worker.postMessage({ type: "repl-eval", id, source });
      });
    },
    /**
     * What can be written at `offset` of the input `source`: resolves with
     * `{from, options, validFor}` or null.
     */
    async complete(source, offset, explicit) {
      try {
        await start();
      } catch {
        return null;
      }
      return new Promise((resolve) => {
        const id = nextId++;
        // An input that is still running keeps the compiler busy.
        const timer = setTimeout(() => settle(id, "resolve", null), COMPLETION_LIMIT);
        pending.set(id, { resolve, reject: () => resolve(null), timer });
        worker.postMessage({ type: "complete", id, request: { mode: "repl", source, offset, explicit } });
      });
    },
    /** Forget everything the session has defined. */
    reset() {
      stop("The session was reset.");
    },
    dispose() {
      stop("The page was closed.");
    },
  };
}
