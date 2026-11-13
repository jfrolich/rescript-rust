import React, { useCallback, useEffect, useMemo, useRef, useState } from "react";
import { EditorState, Prec } from "@codemirror/state";
import { EditorView, drawSelection, highlightSpecialChars, keymap, placeholder } from "@codemirror/view";
import { defaultKeymap, history, historyKeymap } from "@codemirror/commands";
import { bracketMatching, indentUnit, syntaxHighlighting } from "@codemirror/language";
import {
  acceptCompletion,
  closeCompletion,
  completionStatus,
  moveCompletionSelection,
  selectedCompletion,
  startCompletion,
} from "@codemirror/autocomplete";
import { classHighlighter } from "@lezer/highlight";
import { completion } from "./completion.js";
import { codemirrorLanguage, highlight } from "./highlight.jsx";
import { createSession } from "./repl-session.js";

/**
 * How many brackets `text` leaves open, or null when it ends inside a
 * string or a comment.
 */
function openBrackets(text) {
  let depth = 0;
  let index = 0;
  while (index < text.length) {
    const char = text[index];
    const two = text.slice(index, index + 2);
    if (two === "//") {
      const end = text.indexOf("\n", index);
      index = end < 0 ? text.length : end;
    } else if (two === "/*") {
      let open = 1;
      index += 2;
      while (index < text.length && open > 0) {
        if (text.startsWith("/*", index)) (open += 1), (index += 2);
        else if (text.startsWith("*/", index)) (open -= 1), (index += 2);
        else index += 1;
      }
      if (open > 0) return null;
    } else if (char === '"' || char === "`") {
      index += 1;
      while (index < text.length && text[index] !== char) index += text[index] === "\\" ? 2 : 1;
      if (index >= text.length) return null;
      index += 1;
    } else {
      if ("([{".includes(char)) depth += 1;
      else if (")]}".includes(char)) depth -= 1;
      index += 1;
    }
  }
  return depth;
}

/**
 * Whether Enter ends an input: its brackets, strings and comments are
 * closed, and it does not end in something that needs what follows (an
 * operator, an attribute).
 */
export function isComplete(text) {
  const depth = openBrackets(text);
  if (depth === null || depth > 0) return false;
  const end = text.replace(/\/\/[^\n]*$/, "");
  if (/(=>|->|[=|,+\-*/:]|&&|\|\|)\s*$/.test(end)) return false;
  return !/(^|\n)\s*@@?[A-Za-z_][\w.]*(\([^()]*\))?\s*$/.test(end);
}

function Source({ code }) {
  const nodes = useMemo(() => highlight(code, "rescript"), [code]);
  return <code>{nodes}</code>;
}

/** The input line: an editor where Enter evaluates and the arrows walk the history. */
function Prompt({ onSubmit, past, viewRef, onFocus, complete }) {
  const host = useRef(null);
  const state = useRef({ onSubmit, past, onFocus, complete });
  state.current = { onSubmit, past, onFocus, complete };
  // Where in the history the arrows are, and what was typed before them.
  const walk = useRef({ at: null, draft: "" });

  useEffect(() => {
    const replace = (view, text) => {
      view.dispatch({
        changes: { from: 0, to: view.state.doc.length, insert: text },
        selection: { anchor: text.length },
        scrollIntoView: true,
      });
    };
    // A new line starts two spaces in for every bracket that is open.
    const newline = (view) => {
      const { from, to } = view.state.selection.main;
      const depth = openBrackets(view.state.sliceDoc(0, from)) ?? 0;
      const insert = `\n${"  ".repeat(Math.max(0, depth))}`;
      view.dispatch({
        changes: { from, to, insert },
        selection: { anchor: from + insert.length },
        scrollIntoView: true,
        userEvent: "input",
      });
      return true;
    };
    // With the list of completions open, Enter takes the chosen one; when
    // that is what is written already, Enter is for the input.
    const choose = (view) => {
      if (completionStatus(view.state) !== "active") return false;
      const chosen = selectedCompletion(view.state);
      const head = view.state.selection.main.head;
      const written = /[A-Za-z0-9_'.]*$/.exec(view.state.sliceDoc(view.state.doc.lineAt(head).from, head))[0];
      if (chosen && written !== chosen.label && !written.endsWith(`.${chosen.label}`)) return acceptCompletion(view);
      closeCompletion(view);
      return false;
    };
    const submit = (view, always) => {
      if (!always && choose(view)) return true;
      closeCompletion(view);
      const text = view.state.doc.toString();
      if (text.trim() === "") return true;
      if (!always && !isComplete(text)) return newline(view);
      walk.current = { at: null, draft: "" };
      state.current.onSubmit(text.replace(/\s+$/, ""));
      replace(view, "");
      return true;
    };
    // A closing bracket that starts a line goes back to where its line opened.
    const closing = EditorView.inputHandler.of((view, from, to, text) => {
      if (text.length !== 1 || !")]}".includes(text)) return false;
      const line = view.state.doc.lineAt(from);
      if (view.state.sliceDoc(line.from, from).trim() !== "") return false;
      const depth = openBrackets(view.state.sliceDoc(0, line.from));
      if (depth === null) return false;
      const insert = "  ".repeat(Math.max(0, depth - 1)) + text;
      view.dispatch({
        changes: { from: line.from, to, insert },
        selection: { anchor: line.from + insert.length },
        userEvent: "input.type",
      });
      return true;
    });
    const older = (view) => {
      if (completionStatus(view.state) === "active") return moveCompletionSelection(false)(view);
      const { past } = state.current;
      const head = view.state.selection.main.head;
      if (view.state.doc.lineAt(head).number !== 1 || past.length === 0) return false;
      const at = walk.current.at === null ? past.length - 1 : walk.current.at - 1;
      if (at < 0) return true;
      if (walk.current.at === null) walk.current.draft = view.state.doc.toString();
      walk.current.at = at;
      replace(view, past[at]);
      return true;
    };
    const newer = (view) => {
      if (completionStatus(view.state) === "active") return moveCompletionSelection(true)(view);
      const { past } = state.current;
      const head = view.state.selection.main.head;
      if (walk.current.at === null || view.state.doc.lineAt(head).number !== view.state.doc.lines) return false;
      const at = walk.current.at + 1;
      walk.current.at = at >= past.length ? null : at;
      replace(view, at >= past.length ? walk.current.draft : past[at]);
      return true;
    };
    const view = new EditorView({
      parent: host.current,
      state: EditorState.create({
        doc: "",
        extensions: [
          highlightSpecialChars(),
          history(),
          drawSelection(),
          bracketMatching(),
          closing,
          indentUnit.of("  "),
          EditorState.tabSize.of(2),
          syntaxHighlighting(classHighlighter),
          codemirrorLanguage("rescript"),
          placeholder("Type ReScript and press Enter"),
          // Enter and the arrows are the loop's: they choose from the list when it is open.
          completion((...request) => state.current.complete(...request), { keys: false }),
          Prec.highest(
            keymap.of([
              { key: "Enter", run: (target) => submit(target, false), shift: newline },
              { key: "Mod-Enter", run: (target) => submit(target, true) },
              { key: "Tab", run: acceptCompletion },
              { key: "Escape", run: closeCompletion },
              { key: "Ctrl-Space", run: startCompletion },
              { key: "ArrowUp", run: older },
              { key: "ArrowDown", run: newer },
            ]),
          ),
          keymap.of([...defaultKeymap, ...historyKeymap]),
          EditorView.updateListener.of((update) => {
            if (update.focusChanged && update.view.hasFocus) state.current.onFocus?.();
          }),
          EditorView.contentAttributes.of({
            "aria-label": "An input for the ReScript session",
            spellcheck: "false",
            autocapitalize: "off",
            autocorrect: "off",
          }),
        ],
      }),
    });
    viewRef.current = { view, replace: (text) => replace(view, text), submit: () => submit(view, true) };
    return () => {
      viewRef.current = null;
      view.destroy();
    };
  }, [viewRef]);

  return <div className="editor repl-editor" ref={host} />;
}

function Entry({ entry }) {
  const [open, setOpen] = useState(null);
  const lines = entry.input === null ? [] : entry.input.split("\n");
  return (
    <div className={entry.fresh ? "repl-entry fresh" : "repl-entry"}>
      {entry.input !== null && (
        <pre className="repl-source">
          {lines.map((line, index) => (
            <span key={index} className="repl-row">
              <span className="repl-mark" aria-hidden="true">
                {index === 0 ? "›" : "·"}
              </span>
              <Source code={line} />
            </span>
          ))}
        </pre>
      )}
      {entry.pending && <div className="repl-wait">…</div>}
      {entry.output.map((line, index) =>
        line.kind === "value" ? (
          <pre key={index} className="repl-out value">
            <Source code={line.text} />
          </pre>
        ) : (
          <pre key={index} className={`repl-out ${line.kind}`}>
            {line.text}
          </pre>
        ),
      )}
      {(entry.expanded || entry.javascript) && (
        <div className="repl-more">
          {entry.expanded && (
            <button type="button" className={open === "expanded" ? "on" : ""} onClick={() => setOpen(open === "expanded" ? null : "expanded")}>
              expansion
            </button>
          )}
          {entry.javascript && (
            <button type="button" className={open === "javascript" ? "on" : ""} onClick={() => setOpen(open === "javascript" ? null : "javascript")}>
              javascript
            </button>
          )}
        </div>
      )}
      {open === "expanded" && (
        <pre className="repl-detail">
          <Source code={entry.expanded.trim()} />
        </pre>
      )}
      {open === "javascript" && (
        <pre className="repl-detail">
          <code>{highlight(programOf(entry.javascript), "javascript")}</code>
        </pre>
      )}
    </div>
  );
}

/** The JavaScript of an input without the header every file has. */
function programOf(javascript) {
  return javascript.replace(/^\/\/ Generated by ReScript[^\n]*\n+/, "").trim();
}

/**
 * A read-eval-print loop. `intro` is a session that was run when the page
 * was built: it is what the loop shows first, and the compiler runs it again
 * (without a word) when it is loaded, so that its definitions are there.
 *
 * @param libraries  `[{name, source}]`: the modules every session starts with
 * @param intro      `[{input, output, expanded, javascript}]`
 * @param tries      `[{label, source}]`: inputs offered below the loop
 */
export function Repl({ libraries, intro, tries }) {
  const [entries, setEntries] = useState(intro);
  const [busy, setBusy] = useState(false);
  const [status, setStatus] = useState("idle");
  const [note, setNote] = useState(null);
  const [tried, setTried] = useState(0);
  const screen = useRef(null);
  const prompt = useRef(null);
  const nextKey = useRef(intro.length);
  const session = useRef(null);
  const queue = useRef(Promise.resolve());

  const append = useCallback((entry) => {
    setEntries((current) => current.concat({ ...entry, key: nextKey.current++, fresh: true }));
  }, []);

  if (session.current === null) {
    session.current = createSession({
      libraries,
      replay: intro.map((entry) => entry.input),
      onStatus: setStatus,
      // What a timer or a promise of an earlier input prints.
      onLog: (line) => append({ input: null, output: [line] }),
    });
  }
  useEffect(() => () => session.current.dispose(), []);

  // Keep the last line in view.
  useEffect(() => {
    const element = screen.current;
    if (element && entries !== intro) element.scrollTop = element.scrollHeight;
  }, [entries, intro]);

  const evaluate = useCallback((source) => {
    const key = nextKey.current++;
    setEntries((current) => current.concat({ key, input: source, output: [], pending: true, fresh: true }));
    setBusy(true);
    const finish = (result) => {
      setEntries((current) => current.map((entry) => (entry.key === key ? { ...entry, ...result, pending: false } : entry)));
    };
    // One input at a time, in the order they were entered.
    queue.current = queue.current.then(() =>
      session.current
        .evaluate(source)
        .then((result) => {
          finish(result);
          setNote(`Compiled and run in ${Math.max(1, Math.round(result.ms))} ms, in your browser.`);
        })
        .catch((error) => {
          finish({
            output: [
              { kind: "problem", text: error.message },
              { kind: "note", text: "The session starts again: what it had defined is gone." },
            ],
          });
          setNote(null);
        })
        .finally(() => setBusy(false)),
    );
  }, []);

  const reset = () => {
    session.current.reset();
    queue.current = Promise.resolve();
    setEntries(intro);
    setBusy(false);
    setNote(null);
    setTried(0);
    prompt.current?.replace("");
  };

  const past = useMemo(() => entries.filter((entry) => entry.input !== null).map((entry) => entry.input), [entries]);
  const warmUp = () => session.current.warmUp();
  const next = tries[tried] ?? null;

  let foot = "The compiler is loaded when you start typing.";
  if (status === "loading") foot = "Loading the compiler…";
  else if (status === "failed") foot = "The compiler could not be loaded.";
  else if (busy) foot = "Running…";
  else if (note) foot = note;
  else if (status === "ready") foot = "Ready.";

  return (
    <figure className="example repl" onPointerEnter={warmUp}>
      <figcaption className="example-head">
        <div className="example-title">
          <span className="example-kicker">REPL</span>
          <strong>A session</strong>
          <span className="example-summary">Every input is compiled and run. What it defines stays for the next one.</span>
        </div>
        <div className="example-actions">
          {entries !== intro && (
            <button type="button" className="ghost" onClick={reset}>
              Start over
            </button>
          )}
        </div>
      </figcaption>

      <div
        className="repl-screen"
        ref={screen}
        onClick={(event) => {
          // A click on the empty part of the screen is a click on the input.
          if (event.target === event.currentTarget || event.target.classList.contains("repl-input")) prompt.current?.view.focus();
        }}
      >
        {entries.map((entry, index) => (
          <Entry key={entry.key ?? `intro-${index}`} entry={entry} />
        ))}
        <div className="repl-input">
          <span className="repl-mark" aria-hidden="true">
            ›
          </span>
          <Prompt
            onSubmit={evaluate}
            past={past}
            viewRef={prompt}
            onFocus={warmUp}
            complete={(source, offset, explicit) => session.current.complete(source, offset, explicit)}
          />
          <button type="button" className="repl-run" onClick={() => prompt.current?.submit()} aria-label="Run the input">
            Run ↵
          </button>
        </div>
      </div>

      <div className="repl-tries">
        <span className="repl-tries-label">Loaded</span>
        <span className="repl-modules">
          {libraries
            .filter((file) => file.name.endsWith(".res"))
            .map((file) => file.name.replace(/\.res$/, ""))
            .join(" · ")}
        </span>
        {next && (
          <button
            type="button"
            className="ghost repl-try"
            onClick={() => {
              setTried(tried + 1);
              evaluate(next.source);
            }}
          >
            Try: {next.label} →
          </button>
        )}
      </div>

      <div className="example-foot">
        <span className={busy || status === "loading" ? "pulse on" : status === "ready" ? "pulse live" : status === "failed" ? "pulse failed" : "pulse"} />
        {foot}
        <span className="repl-keys">
          <kbd>Enter</kbd> runs, or continues an open bracket · <kbd>Shift</kbd>+<kbd>Enter</kbd> new line · <kbd>Tab</kbd> completes ·{" "}
          <kbd>↑</kbd> earlier inputs
        </span>
      </div>
    </figure>
  );
}
