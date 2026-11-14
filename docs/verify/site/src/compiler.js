/**
 * One compiler worker for the whole page. Every example asks it to build
 * its file; requests run one at a time, and a newer request of the same
 * example replaces one that has not started. The worker (and the
 * WebAssembly module behind it) is created on first use.
 */

const TIME_LIMIT = 20_000;

let worker = null;
let ready = false;
let running = null; // {id, key, resolve, reject, timer}
const waiting = new Map(); // key -> {file, resolve, reject}
let nextId = 1;
const listeners = new Set();
let status = "idle"; // idle | loading | ready | failed

function setStatus(next) {
  status = next;
  for (const listener of listeners) listener(status);
}

export function compilerStatus() {
  return status;
}

export function onCompilerStatus(listener) {
  listeners.add(listener);
  return () => listeners.delete(listener);
}

function start() {
  ready = false;
  setStatus("loading");
  worker = new Worker(new URL("./compiler-worker.js", import.meta.url), { type: "module" });
  worker.onmessage = (event) => {
    const message = event.data;
    if (message.type === "ready") {
      ready = true;
      setStatus("ready");
      next();
    } else if (message.type === "built") {
      if (!running || running.id !== message.id) return;
      const done = running;
      clearTimeout(done.timer);
      running = null;
      if (message.result.crashed) {
        restart();
        done.reject(new Error(message.result.crashed));
      } else {
        done.resolve({ result: message.result, ms: message.ms });
      }
      next();
    } else if (message.type === "failed") {
      fail(`The compiler failed: ${message.message}`);
    }
  };
  worker.onerror = (event) => fail(`The compiler failed: ${event.message || "it could not be loaded"}`);
  worker.postMessage({
    type: "init",
    wasmUrl: new URL("compiler.wasm", document.baseURI).href,
    stdlibUrl: new URL("stdlib.json", document.baseURI).href,
  });
}

function fail(message) {
  const done = running;
  running = null;
  if (done) {
    clearTimeout(done.timer);
    done.reject(new Error(message));
  }
  restart();
}

function restart() {
  if (worker) worker.terminate();
  start();
}

function next() {
  if (!ready || running || waiting.size === 0) return;
  const [key, request] = waiting.entries().next().value;
  waiting.delete(key);
  const id = nextId++;
  const timer = setTimeout(() => {
    fail(`The build was stopped after ${TIME_LIMIT / 1000} seconds.`);
  }, TIME_LIMIT);
  running = { id, key, timer, resolve: request.resolve, reject: request.reject };
  worker.postMessage({ type: "build", id, file: request.file });
}

/** Start loading the compiler, if it is not loaded or loading. */
export function warmUp() {
  if (!worker) start();
}

/**
 * Build `file` (`{name, source}`) for the example `key`. Resolves with
 * `{result, ms}`, or with `null` when a newer request of the same example
 * replaced this one.
 */
export function build(key, file) {
  warmUp();
  return new Promise((resolve, reject) => {
    const replaced = waiting.get(key);
    if (replaced) replaced.resolve(null);
    waiting.set(key, { file, resolve, reject });
    next();
  });
}
