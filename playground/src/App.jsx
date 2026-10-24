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

const INITIAL_CODE = `type shape =
  | Circle({radius: float})
  | Rect({width: float, height: float})

let area = shape =>
  switch shape {
  | Circle({radius}) => Math.Constants.pi *. radius *. radius
  | Rect({width, height}) => width *. height
  }

let total = [Circle({radius: 1.0}), Rect({width: 2.0, height: 3.0})]
  ->Array.map(area)
  ->Array.reduce(0.0, (acc, a) => acc +. a)
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
