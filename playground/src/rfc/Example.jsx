import React, { useCallback, useEffect, useMemo, useRef, useState } from "react";
import TreeView from "../TreeView.jsx";
import { isSourceFile } from "../engine.js";
import { encodeProject } from "../share.js";
import { build as buildProject, compilerStatus, complete as completeProject, onCompilerStatus, warmUp } from "./compiler.js";
import { CodeEditor, selectRange } from "./CodeEditor.jsx";
import { addedLines, Code, languageOf } from "./highlight.jsx";

const INTERNALS = [
  ["parse_tree", "Parse tree"],
  ["typed_tree", "Typed tree"],
  ["raw_lambda", "Raw lambda"],
  ["lambda", "Lambda"],
];

function isInternal(view) {
  return INTERNALS.some(([key]) => key === view);
}

/**
 * A live example: a small project on the left, and on the right what the
 * compiler makes of its main file. It starts from a result that was built
 * with the page; the compiler is loaded when the code is edited or a tree
 * is asked for.
 */
export function Example({ example, prebuilt }) {
  const entry = example.files[example.files.length - 1].name;
  const [files, setFiles] = useState(example.files);
  const [generation, setGeneration] = useState(0);
  const [active, setActive] = useState(entry);
  const [focus, setFocus] = useState(entry);
  const [view, setView] = useState("expanded");
  const [build, setBuild] = useState(prebuilt ?? null);
  const [failure, setFailure] = useState(null);
  const [busy, setBusy] = useState(false);
  const [live, setLive] = useState(false);
  const [ms, setMs] = useState(null);
  const [cursor, setCursor] = useState(null);
  const [status, setStatus] = useState(compilerStatus());
  const sequence = useRef(0);
  const timer = useRef(null);
  const editorView = useRef(null);
  const filesRef = useRef(files);
  filesRef.current = files;

  useEffect(() => onCompilerStatus(setStatus), []);

  const run = useCallback(
    (nextFiles) => {
      const mine = ++sequence.current;
      setBusy(true);
      buildProject(example.id, nextFiles)
        .then((outcome) => {
          if (!outcome || mine !== sequence.current) return;
          setBuild(outcome.result);
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
    [example.id],
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
    setBuild(prebuilt ?? null);
    setFailure(null);
    setBusy(false);
    setLive(false);
    setMs(null);
  };

  const choose = (nextView) => {
    setView(nextView);
    // The trees are not part of the result built with the page.
    if (isInternal(nextView) && !live && !busy) run(filesRef.current);
  };

  const edited = files !== example.files;
  const activeFile = files.find((file) => file.name === active) ?? files[0];
  const sources = files.filter((file) => isSourceFile(file.name));
  const focusFile = sources.find((file) => file.name === focus) ?? sources[sources.length - 1];
  const result = build?.results?.[focusFile.name] ?? null;
  const problems = useMemo(() => {
    if (failure) return [{ file: null, message: failure }];
    if (!build) return [];
    return build.order
      .map((name) => ({ file: name, result: build.results[name] }))
      .filter(({ result }) => result && result.type === "error")
      .map(({ file, result }) => ({ file, message: result.message }));
  }, [build, failure]);
  const warnings = useMemo(() => {
    if (!build) return [];
    return build.order
      .map((name) => build.results[name])
      .filter((result) => result?.type === "success" && result.warnings)
      .map((result) => result.warnings);
  }, [build]);

  let note = "Built with the page. Edit the code to compile it here.";
  if (busy && status !== "ready") note = "Loading the compiler…";
  else if (busy) note = "Compiling…";
  else if (failure) note = "The compiler stopped.";
  else if (live && problems.length > 0) note = "Does not compile: the error is on the right.";
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
          <a className="ghost" href={`playground.html${encodeProject(files)}`} target="_blank" rel="noreferrer">
            Open in playground ↗
          </a>
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
                {file.name}
              </button>
            ))}
            <span className="tabs-hint">editable</span>
          </div>
          <div className="pane-scroll" style={{ "--lines": activeFile.source.split("\n").length }}>
            <CodeEditor
              key={`${generation}/${activeFile.name}`}
              value={activeFile.source}
              language={languageOf(activeFile.name)}
              onChange={edit}
              onCursor={setCursor}
              onFocus={warmUp}
              complete={(source, offset, explicit) =>
                completeProject(
                  filesRef.current.map((file) => (file.name === activeFile.name ? { ...file, source } : file)),
                  activeFile.name,
                  offset,
                  explicit,
                )
              }
              viewRef={editorView}
            />
          </div>
        </section>

        <section className="pane pane-result" aria-label="Result">
          <div className="tabs" role="tablist">
            <button type="button" role="tab" className={view === "expanded" ? "tab active" : "tab"} onClick={() => choose("expanded")}>
              Expanded
            </button>
            <button type="button" role="tab" className={view === "js" ? "tab active" : "tab"} onClick={() => choose("js")}>
              JavaScript
            </button>
            <button
              type="button"
              role="tab"
              className={isInternal(view) ? "tab active" : "tab"}
              onClick={() => choose(isInternal(view) ? view : "typed_tree")}
            >
              Internals
            </button>
            {sources.length > 1 && (
              <label className="focus-file">
                <span>of</span>
                <select value={focusFile.name} onChange={(event) => setFocus(event.target.value)}>
                  {sources.map((file) => (
                    <option key={file.name} value={file.name}>
                      {file.name}
                    </option>
                  ))}
                </select>
              </label>
            )}
          </div>
          {isInternal(view) && (
            <div className="subtabs">
              {INTERNALS.map(([key, label]) => (
                <button key={key} type="button" className={view === key ? "subtab active" : "subtab"} onClick={() => choose(key)}>
                  {label}
                </button>
              ))}
            </div>
          )}
          <div className={busy ? "pane-scroll stale" : "pane-scroll"}>
            <ResultView
              view={view}
              file={focusFile}
              result={result}
              problems={problems}
              busy={busy}
              cursor={active === focusFile.name ? cursor : null}
              onNodeClick={(loc) => {
                if (active !== focusFile.name) setActive(focusFile.name);
                else selectRange(editorView.current, loc);
              }}
            />
          </div>
          <Output logs={build?.logs ?? null} failed={problems.length > 0} warnings={warnings} />
        </section>
      </div>
      <div className="example-foot">
        <span className={busy ? "pulse on" : problems.length > 0 ? "pulse failed" : live ? "pulse live" : "pulse"} />
        {note}
      </div>
    </figure>
  );
}

function ResultView({ view, file, result, problems, busy, cursor, onNodeClick }) {
  if (problems.length > 0) {
    return (
      <div className="problems">
        {problems.map((problem, index) => (
          <pre key={index} className="problem">
            {problem.message}
          </pre>
        ))}
      </div>
    );
  }
  if (!result) return <div className="empty">{busy ? "Compiling…" : "Nothing compiled yet."}</div>;
  if (result.type !== "success") return <div className="empty">{result.message}</div>;
  if (view === "expanded") {
    if (!result.expanded) {
      return (
        <>
          <div className="view-note">This file uses no macro: it is compiled as written.</div>
          <Code code={file.source} language="rescript" />
        </>
      );
    }
    return <Expanded result={result} />;
  }
  if (view === "js") return <Code code={result.js} language="javascript" />;
  const sexp = result[view];
  if (!sexp) return <div className="empty">{busy ? "Compiling…" : "Loading the compiler…"}</div>;
  return <TreeView sexp={sexp} cursorPosition={cursor} onNodeClick={onNodeClick} />;
}

/** The file after expansion, with the lines the macros wrote set apart. */
function Expanded({ result }) {
  const marked = useMemo(
    () => (result.formatted ? addedLines(result.formatted, result.expanded) : null),
    [result.formatted, result.expanded],
  );
  const first = useRef(null);
  // Bring the first generated line into view: it is what the example is about.
  useEffect(() => {
    const scroller = first.current?.closest(".pane-scroll");
    const line = first.current?.querySelector(".line.marked");
    if (!scroller || !line) return;
    const offset = line.getBoundingClientRect().top - scroller.getBoundingClientRect().top + scroller.scrollTop;
    scroller.scrollTop = Math.max(0, offset - 72);
  }, [marked]);
  return (
    <div ref={first}>
      {marked && marked.size > 0 && (
        <div className="legend">
          <span className="legend-mark" />
          written by macros
        </div>
      )}
      <Code code={result.expanded} language="rescript" marked={marked} />
    </div>
  );
}

function Output({ logs, failed, warnings }) {
  return (
    <div className="output">
      <div className="output-label">Output</div>
      {failed || logs === null ? (
        <div className="output-empty">The program runs when every file compiles.</div>
      ) : logs.length === 0 ? (
        <div className="output-empty">The program printed nothing.</div>
      ) : (
        logs.map((log, index) => (
          <pre key={index} className={`output-line ${log.level}`}>
            {log.text}
          </pre>
        ))
      )}
      {warnings.map((warning, index) => (
        <pre key={`w${index}`} className="output-line warn">
          {warning}
        </pre>
      ))}
    </div>
  );
}
