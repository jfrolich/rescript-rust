/**
 * One compiler worker for the whole page. Every example asks it to build
 * its project; requests run one at a time, and a newer request of the same
 * example replaces one that has not started. The worker (and the 10 MB of
 * WebAssembly behind it) is created on first use.
 */

const TIME_LIMIT = 20_000;

let worker = null;
let ready = false;
let running = null; // {id, key, resolve, reject, timer}
const waiting = new Map(); // key -> {files, resolve, reject}
let nextId = 1;
const completions = new Map(); // id -> resolve
const whenReady = []; // what is sent once the compiler has loaded
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
  worker = new Worker(new URL("../compiler-worker.js", import.meta.url), { type: "module" });
  worker.onmessage = (event) => {
    const message = event.data;
    if (message.type === "ready") {
      ready = true;
      setStatus("ready");
      for (const send of whenReady.splice(0)) send();
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
    } else if (message.type === "completed") {
      const resolve = completions.get(message.id);
      completions.delete(message.id);
      if (message.result?.crashed) restart();
      resolve?.(message.result?.crashed ? null : message.result);
    } else if (message.type === "failed") {
      fail(`The compiler failed: ${message.message}`);
    }
  };
  worker.onerror = (event) => fail(`The compiler failed: ${event.message || "it could not be loaded"}`);
  worker.postMessage({ type: "init", stdlibUrl: new URL("stdlib.json", document.baseURI).href });
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
  for (const resolve of completions.values()) resolve(null);
  completions.clear();
  start();
}

function next() {
  if (!ready || running || waiting.size === 0) return;
  const [key, request] = waiting.entries().next().value;
  waiting.delete(key);
  const id = nextId++;
  const timer = setTimeout(() => {
    fail(`The build was stopped after ${TIME_LIMIT / 1000} seconds. A macro or the program probably does not terminate.`);
  }, TIME_LIMIT);
  running = { id, key, timer, resolve: request.resolve, reject: request.reject };
  worker.postMessage({ type: "build", id, files: request.files });
}

/** Start loading the compiler, if it is not loaded or loading. */
export function warmUp() {
  if (!worker) start();
}

/**
 * Build `files` for the example `key`. Resolves with `{result, ms}`, or with
 * `null` when a newer request of the same example replaced this one.
 */
export function build(key, files) {
  warmUp();
  return new Promise((resolve, reject) => {
    const replaced = waiting.get(key);
    if (replaced) replaced.resolve(null);
    waiting.set(key, { files, resolve, reject });
    next();
  });
}

/**
 * What can be written at `offset` of the file `name` of the project
 * `files`. Resolves with `{from, options, validFor}` or null.
 */
export function complete(files, name, offset, explicit) {
  warmUp();
  return new Promise((resolve) => {
    const id = nextId++;
    const timer = setTimeout(() => {
      completions.delete(id);
      resolve(null);
    }, 3000);
    completions.set(id, (result) => {
      clearTimeout(timer);
      resolve(result);
    });
    const send = () => worker.postMessage({ type: "complete", id, request: { mode: "project", files, name, offset, explicit } });
    if (ready) send();
    else whenReady.push(send);
  });
}
