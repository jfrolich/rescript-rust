import React, { useCallback, useEffect, useRef, useState } from "react";
import { build as buildFile, compilerStatus, onCompilerStatus, warmUp } from "./compiler.js";
import { CodeEditor } from "./CodeEditor.jsx";
import { Code } from "./highlight.jsx";

/**
 * A live example: a ReScript file on the left, and on the right what the
 * compiler makes of it: the JavaScript, or the report. It starts from a
 * result that was built with the page; the compiler is loaded when the code
 * is edited.
 */
export function Example({ example, prebuilt }) {
  const [source, setSource] = useState(example.source);
  const [generation, setGeneration] = useState(0);
  const [result, setResult] = useState(prebuilt ?? null);
  const [failure, setFailure] = useState(null);
  const [busy, setBusy] = useState(false);
  const [live, setLive] = useState(false);
  const [ms, setMs] = useState(null);
  const [status, setStatus] = useState(compilerStatus());
  const sequence = useRef(0);
  const timer = useRef(null);

  useEffect(() => onCompilerStatus(setStatus), []);

  const run = useCallback(
    (nextSource) => {
      const mine = ++sequence.current;
      setBusy(true);
      buildFile(example.id, { name: example.name, source: nextSource })
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
    [example.id, example.name],
  );

  const edit = (value) => {
    setSource(value);
    clearTimeout(timer.current);
    timer.current = setTimeout(() => run(value), 250);
  };

  const reset = () => {
    clearTimeout(timer.current);
    sequence.current += 1;
    setSource(example.source);
    setGeneration((value) => value + 1);
    setResult(prebuilt ?? null);
    setFailure(null);
    setBusy(false);
    setLive(false);
    setMs(null);
  };

  const edited = source !== example.source;
  const failed = Boolean(failure) || (result && result.type !== "success");

  let note = example.fails
    ? "Built with the page. The compiler rejects it, which is what the example shows. Edit the code to compile it here."
    : "Built with the page. Edit the code to compile it here.";
  if (busy && status !== "ready") note = "Loading the compiler…";
  else if (busy) note = "Compiling…";
  else if (failure) note = "The compiler stopped.";
  else if (live && failed) note = "Rejected: the report is on the right.";
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
            <button type="button" role="tab" aria-selected="true" className="tab active">
              {example.name}
            </button>
            <span className="tabs-hint">editable</span>
          </div>
          <div className="pane-scroll" style={{ "--lines": Math.min(source.split("\n").length, 30) }}>
            <CodeEditor key={generation} value={source} language="rescript" onChange={edit} onFocus={warmUp} />
          </div>
        </section>

        <section className="pane pane-result" aria-label="Result">
          <div className="tabs" role="tablist">
            <button type="button" role="tab" aria-selected="true" className="tab active">
              {failed ? "Rejected" : "JavaScript"}
            </button>
          </div>
          <div className={busy ? "pane-scroll stale" : "pane-scroll"}>
            <ResultView result={result} failure={failure} busy={busy} expected={example.expected} />
          </div>
          {result?.warnings && (
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
      </div>
    </figure>
  );
}

/** `expected` says why an example that is meant to be rejected is. */
function ResultView({ result, failure, busy, expected }) {
  if (failure) {
    return (
      <div className="problems">
        <pre className="problem">{failure}</pre>
      </div>
    );
  }
  if (!result) return <div className="empty">{busy ? "Compiling…" : "Nothing compiled yet."}</div>;
  if (result.type !== "success") {
    return (
      <div className="problems">
        {expected && <p className="expected">{expected}</p>}
        <pre className="problem">{result.message}</pre>
      </div>
    );
  }
  return <Code code={result.js} language="javascript" />;
}
