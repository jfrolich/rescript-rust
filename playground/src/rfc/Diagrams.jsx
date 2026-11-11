import React from "react";

/** How a file is compiled: the flowchart of the "How it runs" section. */
export function FlowDiagram() {
  return (
    <figure className="flow" aria-label="How a file with macros is compiled">
      <div className="flow-row">
        <div className="flow-node">
          <b>Main.res</b>
          <span>the file as written</span>
        </div>
        <div className="flow-arrow" />
        <div className="flow-node">
          <b>Parse and type check</b>
          <span>stops at the first macro use</span>
        </div>
        <div className="flow-arrow">
          <em>no macro used</em>
        </div>
        <div className="flow-node flow-out">
          <b>JavaScript</b>
          <span>one pass, as before</span>
        </div>
      </div>
      <div className="flow-drop">
        <em>a macro is used</em>
      </div>
      <div className="flow-row">
        <div className="flow-spacer" />
        <div className="flow-arrow flow-none" />
        <div className="flow-node flow-accent">
          <b>Expansion pass</b>
          <span>type check, run each macro, record its result as an edit of the text</span>
        </div>
        <div className="flow-arrow flow-both">
          <em>call · answer</em>
        </div>
        <div className="flow-node flow-engine">
          <b>JavaScript engine</b>
          <span>the macro's compiled module</span>
        </div>
      </div>
      <div className="flow-notes">
        <div>
          <b>Edits?</b> Apply them to the source text and run another pass.
        </div>
        <div>
          <b>No edits?</b> Compile the expanded text like any file, with every position mapped back to the file as
          written.
        </div>
      </div>
    </figure>
  );
}

/** A Mermaid `sequenceDiagram`, drawn as rows of messages between lanes. */
export function SequenceDiagram({ source }) {
  const participants = [];
  const rows = [];
  let depth = 0;
  for (const raw of source.split("\n")) {
    const line = raw.trim();
    let match;
    if ((match = /^participant (\w+)(?: as (.+))?$/.exec(line))) {
      participants.push({ id: match[1], label: match[2] ?? match[1] });
    } else if ((match = /^loop (.+)$/.exec(line))) {
      rows.push({ type: "loop", text: match[1] });
      depth += 1;
    } else if (line === "end") {
      depth = Math.max(0, depth - 1);
    } else if ((match = /^(\w+)(-->>|->>)(\w+): (.+)$/.exec(line))) {
      rows.push({ type: "message", from: match[1], to: match[3], reply: match[2] === "-->>", text: match[4], depth });
    }
  }
  const column = (id) => participants.findIndex((participant) => participant.id === id);
  return (
    <figure className="sequence" style={{ "--lanes": participants.length }}>
      <div className="sequence-head">
        {participants.map((participant) => (
          <div key={participant.id}>{participant.label}</div>
        ))}
      </div>
      {rows.map((row, index) => {
        if (row.type === "loop") {
          return (
            <div key={index} className="sequence-loop">
              ↻ {row.text}
            </div>
          );
        }
        const from = column(row.from);
        const to = column(row.to);
        const start = Math.min(from, to);
        const end = Math.max(from, to);
        const classes = ["sequence-message"];
        if (row.reply) classes.push("reply");
        if (to < from) classes.push("left");
        if (from === to) classes.push("self");
        return (
          <div key={index} className={row.depth ? "sequence-row in-loop" : "sequence-row"}>
            <div className={classes.join(" ")} style={{ gridColumn: `${start + 1} / ${end + 2}`, "--span": end - start + 1 }}>
              <span>{row.text}</span>
            </div>
          </div>
        );
      })}
    </figure>
  );
}

const COSTS = [
  { label: "Run a derive-style macro", detail: "10-field record, 41 questions to the compiler", micros: 14, kind: "macro" },
  { label: "Load a macro module", detail: "once per engine", micros: 84, kind: "macro" },
  { label: "Create a QuickJS engine", detail: "once per compiler thread", micros: 92, kind: "macro" },
  { label: "Start ppx-spice", detail: "a PPX is started once per file", micros: 6100, kind: "process" },
  { label: "Start Node", detail: "for comparison", micros: 70000, kind: "process" },
];

function time(micros) {
  if (micros < 1000) return `${micros} µs`;
  return `${(micros / 1000).toFixed(micros < 10000 ? 1 : 0)} ms`;
}

/** The cost table as bars on a logarithmic scale. */
export function CostChart() {
  const min = Math.log10(5);
  const max = Math.log10(100000);
  return (
    <figure className="chart">
      {COSTS.map((cost) => (
        <div key={cost.label} className="chart-row">
          <div className="chart-label">
            <b>{cost.label}</b>
            <span>{cost.detail}</span>
          </div>
          <div className="chart-track">
            <div
              className={`chart-bar ${cost.kind}`}
              style={{ width: `${((Math.log10(cost.micros) - min) / (max - min)) * 100}%` }}
            />
            <span className="chart-value">{time(cost.micros)}</span>
          </div>
        </div>
      ))}
      <figcaption>Logarithmic scale: each step to the right is ten times slower.</figcaption>
    </figure>
  );
}
