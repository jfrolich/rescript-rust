import React, { useState, useEffect, useRef, useCallback } from "react";
import { Tabs } from "@base-ui/react/tabs";
import Editor, { loader } from "@monaco-editor/react";
import { parseSexp, buildLocationIndex, findNodeAtCursor } from "./sexp-parser.js";
import TreeView from "./TreeView.jsx";
import { registerRescriptLanguage, languageId } from "./rescript-language.js";
import { loadStdlib } from "./stdlib-loader.js";

// Register ReScript language with Monaco before any editor mounts
loader.init().then((monaco) => {
  registerRescriptLanguage(monaco);
});

const INITIAL_CODE = `// ── Comptime playground ─────────────────────────────────────────────────
// Functions marked @comptime run at compile time. @typeInfo introspects a
// type; inline for unrolls loops. Each call monomorphizes to a specialized
// function — recursive types produce self-recursive code, no infinite
// expansion.

type address = { street: string, city: string }
type status = Active | Inactive | Pending
type user = { name: string, age: int, active: bool, status: status, address: address }
type tree = { value: string, children: array<tree> }

exception DecodeError(string)

// Variants encode as [name, ...constructor_arguments]. For enum-style
// variants the arguments list is empty, so the JSON is just [name].
// getTag reads the tag regardless of whether the value has arguments
// (ReScript compiles payload-free variants to a plain string, and
// payload-carrying variants to {TAG: name, _0, _1, ...}).
let getTag: 'a => string = %raw(`function(v) {
  return typeof v === "string" ? v : v.TAG;
}`)

let getArg: ('a, int) => JSON.t = %raw(`function(v, i) {
  return v["_" + i];
}`)

// ── 1. Zero-overhead JSON encoder ───────────────────────────────────────
// encode(alice) produces a specialized encode$user function. Since the
// JSON.Encode.* helpers are %identity, the output reduces to plain Dict
// assignments — no runtime type dispatch.

@comptime
let rec encode = (value): JSON.t => {
  switch @typeInfo(value) {
  | String => JSON.Encode.string(value)
  | Int => JSON.Encode.int(value)
  | Bool => JSON.Encode.bool(value)
  | Record({fields}) =>
    let dict = Dict.make()
    inline for field in fields {
      Dict.set(dict, field.name, encode(@field(value, field.name)))
    }
    JSON.Encode.object(dict)
  | Variant({constructors}) =>
    let tag = getTag(value)
    let result = ref(JSON.Null)
    inline for c in constructors {
      if tag == c.name {
        let arr = [JSON.Encode.string(c.name)]
        let idx = ref(0)
        inline for _argType in c.args {
          Array.push(arr, getArg(value, idx.contents))
          idx := idx.contents + 1
        }
        result := JSON.Encode.array(arr)
      }
    }
    result.contents
  | Array(_) => JSON.Encode.array(Array.map(value, v => encode(v)))
  | _ => @compileError("encode: unsupported type")
  }
}

let alice: user = {
  name: "Alice",
  age: 30,
  active: true,
  status: Active,
  address: {street: "Main St", city: "NYC"},
}

let aliceJson = encode(alice)

// Recursive types: encode$tree calls itself via Array.map.
let myTree: tree = {
  value: "root",
  children: [
    {value: "child1", children: []},
    {value: "child2", children: []},
  ],
}
let treeJson = encode(myTree)

// ── 2. Decoder with explicit type parameter ─────────────────────────────
// The decoder has no value to infer from, so it takes a comptime type
// parameter: decode(user, json) specializes to decode$user. On mismatch
// it throws DecodeError; wrap the call in try/catch to get an option.

@comptime
let rec decode = (type t, json: JSON.t) => {
  switch @typeInfo(t) {
  | String =>
    switch json { | String(s) => s | _ => throw(DecodeError("expected string")) }
  | Int =>
    switch json { | Number(n) => Float.toInt(n) | _ => throw(DecodeError("expected int")) }
  | Bool =>
    switch json { | Boolean(b) => b | _ => throw(DecodeError("expected bool")) }
  | Record({fields}) =>
    switch json {
    | Object(dict) =>
      @record(t, inline for field in fields {
        decode(field.typ, Dict.getUnsafe(dict, field.name))
      })
    | _ => throw(DecodeError("expected object"))
    }
  | Variant({constructors}) =>
    switch json {
    | Array(items) =>
      switch items[0] {
      | Some(String(name)) =>
        let result = ref(None)
        inline for c in constructors {
          if name == c.name { result := Some(@constructor(t, c.name)) }
        }
        switch result.contents {
        | Some(v) => v
        | None => throw(DecodeError("unknown variant: " ++ name))
        }
      | _ => throw(DecodeError("expected [name, ...] array"))
      }
    | _ => throw(DecodeError("expected variant array"))
    }
  | _ => @compileError("decode: unsupported type")
  }
}

let decodedAlice = try Some(decode(user, aliceJson)) catch {
| DecodeError(_) => None
}

// ── 3. Type-level comptime: keys of a record as a variant ───────────────
// @buildVariant consumes a list of @variantCase specs to emit a real
// variant type at compile time.

@comptime
let userKey =
  switch @typeInfo(user) {
  | Record({fields}) =>
    @buildVariant(inline for field in fields {
      @variantCase({name: field.name})
    })
  | _ => @compileError("expected record")
  }

let k1: userKey = Name
let k2: userKey = Age
`;

const TAB_LABELS = {
  parse_tree: "Parse Tree",
  typed_tree: "Typed Tree",
  raw_lambda: "Raw Lambda",
  lambda: "Lambda",
  js: "JavaScript",
};

export default function App() {
  const [compiler, setCompiler] = useState(null);
  const [status, setStatus] = useState("Loading WASM...");
  const [statusType, setStatusType] = useState("loading");
  const [result, setResult] = useState(null);
  const [compileTime, setCompileTime] = useState(null);
  const [activeTab, setActiveTab] = useState("parse_tree");
  const [cursorPosition, setCursorPosition] = useState({ line: 1, col: 0 });
  const [editorWidth, setEditorWidth] = useState(50);
  const editorRef = useRef(null);
  const resizing = useRef(false);
  const compileTimer = useRef(null);

  // Load WASM compiler + stdlib
  useEffect(() => {
    async function loadCompiler() {
      try {
        setStatus("Loading WASM...");
        const wasm = await import("../crate/pkg/rescript_playground_wasm.js");
        await wasm.default();

        setStatus("Loading stdlib...");
        const fileCount = await loadStdlib(wasm);
        console.log(`Loaded ${fileCount} stdlib files into VFS`);

        setCompiler(wasm);
        setStatus("Ready");
        setStatusType("ready");

        // Initial compile
        const t0 = performance.now();
        const output = wasm.compile_all(INITIAL_CODE, "Playground.res");
        setCompileTime(Math.round(performance.now() - t0));
        setResult(JSON.parse(output));
      } catch (err) {
        console.error("Failed to load:", err);
        setStatus(`Failed: ${err.message}`);
        setStatusType("error");
      }
    }
    loadCompiler();
  }, []);

  // Compile on editor change (debounced)
  const handleEditorChange = useCallback(
    (value) => {
      if (!compiler) return;
      clearTimeout(compileTimer.current);
      compileTimer.current = setTimeout(() => {
        const t0 = performance.now();
        const output = compiler.compile_all(value || "", "Playground.res");
        setCompileTime(Math.round(performance.now() - t0));
        setResult(JSON.parse(output));
      }, 300);
    },
    [compiler]
  );

  // Cursor position tracking
  const handleEditorMount = useCallback((editor) => {
    editorRef.current = editor;
    editor.onDidChangeCursorPosition((e) => {
      setCursorPosition({
        line: e.position.lineNumber,
        col: e.position.column - 1,
      });
    });
  }, []);

  // Handle tree node click -> select in editor
  const handleNodeClick = useCallback((loc) => {
    const editor = editorRef.current;
    if (!editor || !loc) return;
    editor.setSelection({
      startLineNumber: loc.startLine,
      startColumn: loc.startCol + 1,
      endLineNumber: loc.endLine,
      endColumn: loc.endCol + 1,
    });
    editor.revealLineInCenter(loc.startLine);
  }, []);

  // Resize handle
  useEffect(() => {
    const handleMouseMove = (e) => {
      if (!resizing.current) return;
      const pct = (e.clientX / window.innerWidth) * 100;
      setEditorWidth(Math.max(20, Math.min(80, pct)));
    };
    const handleMouseUp = () => {
      resizing.current = false;
      document.body.style.cursor = "";
      document.body.style.userSelect = "";
    };
    window.addEventListener("mousemove", handleMouseMove);
    window.addEventListener("mouseup", handleMouseUp);
    return () => {
      window.removeEventListener("mousemove", handleMouseMove);
      window.removeEventListener("mouseup", handleMouseUp);
    };
  }, []);

  const handleResizeStart = () => {
    resizing.current = true;
    document.body.style.cursor = "col-resize";
    document.body.style.userSelect = "none";
  };

  // Get current sexp content for the active tree tab
  const currentSexp = result?.[activeTab] || "";
  const isTreeTab = activeTab !== "js";

  return (
    <div className="app">
      <header className="header">
        <div className="header-left">
          <h1>ReScript Playground</h1>
          <span className="badge">Rust Compiler</span>
        </div>
        <div className="header-right">
          <span className={`status ${statusType}`}>{status}</span>
          {compileTime !== null && (
            <span className="compile-time">{compileTime}ms</span>
          )}
        </div>
      </header>

      <div className="main">
        <div className="editor-pane" style={{ width: `${editorWidth}%` }}>
          <Editor
            defaultLanguage={languageId}
            defaultValue={INITIAL_CODE}
            theme="vs-dark"
            onChange={handleEditorChange}
            onMount={handleEditorMount}
            options={{
              minimap: { enabled: false },
              fontSize: 14,
              fontFamily: "'Cascadia Code', 'Fira Code', 'Consolas', monospace",
              lineNumbers: "on",
              scrollBeyondLastLine: false,
              automaticLayout: true,
              padding: { top: 12 },
              renderLineHighlight: "gutter",
            }}
          />
        </div>

        <div
          className="resize-handle"
          onMouseDown={handleResizeStart}
        />

        <div className="output-pane" style={{ flex: 1 }}>
          <Tabs.Root value={activeTab} onValueChange={setActiveTab}>
            <Tabs.List className="tabs-list">
              {Object.entries(TAB_LABELS).map(([key, label]) => (
                <Tabs.Tab key={key} value={key} className="tabs-tab">
                  {label}
                </Tabs.Tab>
              ))}
              <Tabs.Indicator className="tabs-indicator" />
            </Tabs.List>

            {Object.keys(TAB_LABELS).map((key) => (
              <Tabs.Panel key={key} value={key} className="tabs-panel" keepMounted>
                {result?.type === "error" && result?.stage !== undefined && (
                  <ErrorDisplay result={result} tabKey={key} />
                )}
                {key === "js" ? (
                  <JsOutput code={result?.js || ""} />
                ) : (
                  <TreePanel
                    sexp={result?.[key] || ""}
                    cursorPosition={cursorPosition}
                    onNodeClick={handleNodeClick}
                  />
                )}
              </Tabs.Panel>
            ))}
          </Tabs.Root>
        </div>
      </div>
    </div>
  );
}

function ErrorDisplay({ result, tabKey }) {
  const stages = ["parse", "ppx", "typecheck", "lambda", "js"];
  const errorStageIdx = stages.indexOf(result.stage);
  const tabStageMap = {
    parse_tree: 0,
    typed_tree: 2,
    raw_lambda: 3,
    lambda: 3,
    js: 4,
  };
  const tabStageIdx = tabStageMap[tabKey] ?? 0;

  // Only show error on tabs at or after the failing stage
  if (tabStageIdx < errorStageIdx) return null;
  if (result[tabKey]) return null; // Has partial data

  return (
    <div className="error-container">
      <div className="error-title">
        {result.stage} error
      </div>
      {result.errors?.map((err, i) => (
        <div key={i} className="error-message">{err}</div>
      ))}
    </div>
  );
}

function TreePanel({ sexp, cursorPosition, onNodeClick }) {
  if (!sexp) {
    return <div className="empty-panel">No data</div>;
  }

  return (
    <TreeView
      sexp={sexp}
      cursorPosition={cursorPosition}
      onNodeClick={onNodeClick}
    />
  );
}

function JsOutput({ code }) {
  if (!code) {
    return <div className="empty-panel">No JavaScript output</div>;
  }

  return (
    <div className="js-output">
      <Editor
        language="javascript"
        value={code}
        theme="vs-dark"
        options={{
          readOnly: true,
          minimap: { enabled: false },
          fontSize: 13,
          fontFamily: "'Cascadia Code', 'Fira Code', 'Consolas', monospace",
          lineNumbers: "on",
          scrollBeyondLastLine: false,
          automaticLayout: true,
          padding: { top: 8 },
          renderLineHighlight: "none",
          domReadOnly: true,
        }}
      />
    </div>
  );
}
