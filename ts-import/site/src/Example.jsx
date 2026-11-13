import React, { useCallback, useEffect, useMemo, useRef, useState } from "react";
import { build as buildFiles, compilerStatus, onCompilerStatus, warmUp } from "./compiler.js";
import { CodeEditor } from "./CodeEditor.jsx";
import { addedLines, Code, languageOf } from "./highlight.jsx";

/** `node_modules/tiny-money/index.d.ts` is shown as `tiny-money/index.d.ts`. */
function label(name) {
  return name.replace(/^node_modules\//, "");
}

/**
 * A live example: TypeScript files and a ReScript file on the left, and on
 * the right what the compiler makes of the ReScript file. It starts from a
 * result that was built with the page; the compiler is loaded when the code
 * is edited.
 *
 * An example marked `plain` imports nothing from TypeScript: its result is
 * the JavaScript, or the error, alone.
 */
export function Example({ example, prebuilt }) {
  const entry = example.files[example.files.length - 1].name;
  const [files, setFiles] = useState(example.files);
  const [generation, setGeneration] = useState(0);
  const [active, setActive] = useState(example.open ?? entry);
  const [view, setView] = useState(example.plain ? "js" : (example.view ?? "expanded"));
  const [result, setResult] = useState(prebuilt ?? null);
  const [failure, setFailure] = useState(null);
  const [busy, setBusy] = useState(false);
  const [live, setLive] = useState(false);
  const [ms, setMs] = useState(null);
  const [status, setStatus] = useState(compilerStatus());
  const sequence = useRef(0);
  const timer = useRef(null);
  const filesRef = useRef(files);
  filesRef.current = files;

  useEffect(() => onCompilerStatus(setStatus), []);

  const run = useCallback(
    (nextFiles) => {
      const mine = ++sequence.current;
      setBusy(true);
      buildFiles(example.id, nextFiles, Boolean(example.compare))
        .then((outcome) => {
          if (!outcome || mine !== sequence.current) return;
          setResult(outcome.result);
          setMs(Math.round(outcome.ms));
          setFailure(null);
          setLive(true);
          setBusy(false);
        })
        .catch((error) => {
          if (mine !== sequence.current) return;
          setFailure(error.message);
          setBusy(false);
        });
    },
    [example.id, example.compare],
  );

  const edit = (value) => {
    const nextFiles = filesRef.current.map((file) => (file.name === active ? { ...file, source: value } : file));
    setFiles(nextFiles);
    clearTimeout(timer.current);
    timer.current = setTimeout(() => run(nextFiles), 250);
  };

  const reset = () => {
    clearTimeout(timer.current);
    sequence.current += 1;
    setFiles(example.files);
    setGeneration((value) => value + 1);
    setResult(prebuilt ?? null);
    setFailure(null);
    setBusy(false);
    setLive(false);
    setMs(null);
  };

  const edited = files !== example.files;
  const activeFile = files.find((file) => file.name === active) ?? files[0];
  const source = files[files.length - 1].source;
  const failed = Boolean(failure) || (result && result.type !== "success");
  const notes = useMemo(() => (result?.imports ?? []).flatMap((entry) => entry.notes), [result]);

  let note = example.fails
    ? "Built with the page. It does not compile, which is what the example shows. Edit the code to compile it here."
    : "Built with the page. Edit the code to compile it here.";
  if (busy && status !== "ready") note = "Loading the compiler…";
  else if (busy) note = "Compiling…";
  else if (failure) note = "The compiler stopped.";
  else if (live && failed) note = "Does not compile: the error is on the right.";
  else if (live && ms !== null) note = `Compiled in ${ms} ms, in your browser.`;

  return (
    <figure className="example" onPointerEnter={warmUp}>
      <figcaption className="example-head">
        <div className="example-title">
          <span className="example-kicker">Example</span>
          <strong>{example.title}</strong>
          <span className="example-summary">{example.summary}</span>
        </div>
        <div className="example-actions">
          {edited && (
            <button type="button" className="ghost" onClick={reset}>
              Reset
            </button>
          )}
        </div>
      </figcaption>

      <div className="example-body">
        <section className="pane pane-source" aria-label="Source">
          <div className="tabs" role="tablist">
            {files.map((file) => (
              <button
                key={file.name}
                type="button"
                role="tab"
                aria-selected={file.name === activeFile.name}
                className={file.name === activeFile.name ? "tab active" : "tab"}
                onClick={() => setActive(file.name)}
              >
                {label(file.name)}
              </button>
            ))}
            <span className="tabs-hint">editable</span>
          </div>
          <div className="pane-scroll" style={{ "--lines": Math.min(activeFile.source.split("\n").length, 30) }}>
            <CodeEditor
              key={`${generation}/${activeFile.name}`}
              value={activeFile.source}
              language={languageOf(activeFile.name)}
              onChange={edit}
              onFocus={warmUp}
            />
          </div>
        </section>

        <section className="pane pane-result" aria-label="Result">
          <div className="tabs" role="tablist">
            {!example.plain && (
              <Tab view="expanded" current={view} choose={setView}>
                As ReScript
              </Tab>
            )}
            <Tab view="js" current={view} choose={setView}>
              {example.plain && failed ? (example.fails ? "Rejected today" : "Error") : "JavaScript"}
            </Tab>
            {!example.plain && (
              <Tab view="typescript" current={view} choose={setView}>
                TypeScript
                {notes.length > 0 && <span className="tab-count">{notes.length}</span>}
              </Tab>
            )}
          </div>
          <div className={busy ? "pane-scroll stale" : "pane-scroll"}>
            <ResultView
              view={view}
              source={source}
              result={result}
              failure={failure}
              busy={busy}
              notes={notes}
              expected={example.expected}
            />
          </div>
          {result?.warnings && view !== "typescript" && (
            <div className="output">
              <div className="output-label">Warnings</div>
              <pre className="output-line warn">{result.warnings}</pre>
            </div>
          )}
        </section>
      </div>
      <div className="example-foot">
        <span className={busy ? "pulse on" : failed ? "pulse failed" : live ? "pulse live" : "pulse"} />
        {note}
        {result?.stats && result.imports.length > 0 && <Cost stats={result.stats} full={result.full} />}
      </div>
    </figure>
  );
}

function Tab({ view, current, choose, children }) {
  return (
    <button type="button" role="tab" className={view === current ? "tab active" : "tab"} onClick={() => choose(view)}>
      {children}
    </button>
  );
}

/** `expected` says why an example that is meant not to compile does not. */
function ResultView({ view, source, result, failure, busy, notes, expected }) {
  if (failure) {
    return (
      <div className="problems">
        <pre className="problem">{failure}</pre>
      </div>
    );
  }
  if (!result) return <div className="empty">{busy ? "Compiling…" : "Nothing compiled yet."}</div>;
  if (view === "typescript") return <TypeScriptView result={result} notes={notes} />;
  const problem = result.type !== "success" && (
    <div className="problems">
      {expected && <p className="expected">{expected}</p>}
      <pre className="problem">{result.message}</pre>
    </div>
  );
  if (view === "js") {
    return problem || <Code code={result.js} language="javascript" />;
  }
  // The imports are shown even when the file then fails to type check: the
  // error is about the types on this side.
  return (
    <>
      {problem}
      {result.expanded ? <Expanded source={source} expanded={result.expanded} /> : null}
    </>
  );
}

/** The file with its imports written out, the written lines set apart. */
function Expanded({ source, expanded }) {
  const marked = useMemo(() => addedLines(source, expanded), [source, expanded]);
  return (
    <div>
      {marked.size > 0 && (
        <div className="legend">
          <span className="legend-mark" />
          what the import stands for
        </div>
      )}
      <Code code={expanded} language="rescript" marked={marked} />
    </div>
  );
}

function time(micros) {
  if (micros < 1000) return `${(micros / 1000).toFixed(2)} ms`;
  if (micros < 10000) return `${(micros / 1000).toFixed(1)} ms`;
  return `${Math.round(micros / 1000)} ms`;
}

function plural(count, word) {
  return `${count.toLocaleString("en")} ${word}${count === 1 ? "" : "s"}`;
}

/** In the footer: how much of TypeScript the import needed. */
function Cost({ stats, full }) {
  return (
    <span className="cost">
      {plural(stats.types, "type")} resolved
      {full && full.types > stats.types && <> of {full.types.toLocaleString("en")} in a full check</>}
    </span>
  );
}

function Bar({ label: text, value, total, detail, accent }) {
  const width = total > 0 ? Math.max(1.5, (value / total) * 100) : 0;
  return (
    <div className="bar-row">
      <span className="bar-label">{text}</span>
      <span className="bar-track">
        <span className={accent ? "bar-fill accent" : "bar-fill"} style={{ width: `${width}%` }} />
      </span>
      <span className="bar-value">{detail}</span>
    </div>
  );
}

function TypeScriptView({ result, notes }) {
  const { stats, full } = result;
  const errors = result.imports.filter((entry) => entry.error);
  // Not counting the declarations of TypeScript itself, nor the few lines
  // that import the modules for the compiler.
  const own = Math.max(0, stats.files - stats.lib_files - 1);
  return (
    <div className="ts-view">
      {errors.map((entry, index) => (
        <pre key={index} className="problem">
          {entry.error}
        </pre>
      ))}
      <div className="ts-block">
        <div className="output-label">What TypeScript did</div>
        <p className="ts-line">
          Read {plural(own, "file")} ({plural(stats.lines, "line")}) and its standard library declarations, then
          resolved the types of the imported names only.
        </p>
        {full && (
          <div className="bars">
            <Bar
              accent
              label="This import"
              value={stats.types}
              total={Math.max(full.types, stats.types)}
              detail={`${plural(stats.types, "type")} · ${time(stats.micros)}`}
            />
            <Bar
              label="Full check"
              value={full.types}
              total={Math.max(full.types, stats.types)}
              detail={`${plural(full.types, "type")} · ${time(full.micros)}`}
            />
          </div>
        )}
        {full && full.errors > 0 && (
          <p className="ts-line">
            A full check of these files reports {plural(full.errors, "error")}. The import does not look at the code
            they are in.
          </p>
        )}
      </div>
      <div className="ts-block">
        <div className="output-label">Where ReScript says less than TypeScript</div>
        {notes.length === 0 ? (
          <p className="ts-line">Nowhere: every type of this import has an exact ReScript form.</p>
        ) : (
          <ul className="notes">
            {notes.map((entry, index) => (
              <li key={index}>
                <div className="note-head">
                  <span className="note-gap">{entry.gap}</span>
                  <code>{entry.subject}</code>
                  {entry.path && <span className="note-path">{entry.path}</span>}
                </div>
                <div className="note-message">{entry.message}</div>
                {entry.ts && <code className="note-ts">{entry.ts}</code>}
              </li>
            ))}
          </ul>
        )}
      </div>
    </div>
  );
}
