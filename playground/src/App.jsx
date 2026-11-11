import React, { useState, useEffect, useRef, useCallback, useMemo } from "react";
import { Tabs } from "@base-ui/react/tabs";
import Editor, { loader } from "@monaco-editor/react";
import TreeView from "./TreeView.jsx";
import { registerRescriptLanguage, languageId } from "./rescript-language.js";
import { createCompiler } from "./compiler-client.js";
import { isSourceFile } from "./engine.js";
import { examples } from "./examples.js";
import { decodeProject, encodeProject } from "./share.js";

// Register ReScript language with Monaco before any editor mounts
let monacoInstance = null;
loader.init().then((monaco) => {
  monacoInstance = monaco;
  registerRescriptLanguage(monaco);
});

const TABS = [
  ["expanded", "Expanded"],
  ["js", "JavaScript"],
  ["output", "Output"],
  ["parse_tree", "Parse Tree"],
  ["typed_tree", "Typed Tree"],
  ["raw_lambda", "Raw Lambda"],
  ["lambda", "Lambda"],
];

const EDITOR_OPTIONS = {
  minimap: { enabled: false },
  fontSize: 14,
  fontFamily: "'Cascadia Code', 'Fira Code', 'Consolas', monospace",
  lineNumbers: "on",
  scrollBeyondLastLine: false,
  automaticLayout: true,
  padding: { top: 12 },
  renderLineHighlight: "gutter",
};

const READONLY_OPTIONS = {
  ...EDITOR_OPTIONS,
  fontSize: 13,
  readOnly: true,
  domReadOnly: true,
  renderLineHighlight: "none",
  padding: { top: 8 },
  wordWrap: "on",
  wrappingIndent: "deepIndent",
};

function languageOf(filename) {
  if (filename.endsWith(".res") || filename.endsWith(".resi")) return languageId;
  if (filename.endsWith(".json")) return "json";
  return "plaintext";
}

function initialProject() {
  const shared = decodeProject(window.location.hash);
  if (shared) return { exampleId: "", files: shared };
  return { exampleId: examples[0].id, files: examples[0].files };
}

/** The first location of a compiler message: `Main.res:3:10-14`. */
function locationOf(message) {
  const found = /^\s*\S+?:(\d+):(\d+)(?:-(\d+)(?::(\d+))?)?\s*$/m.exec(message);
  if (!found) return null;
  const [, line, column, third, fourth] = found;
  const startLine = Number(line);
  const startColumn = Number(column);
  if (fourth !== undefined) {
    return { startLine, startColumn, endLine: Number(third), endColumn: Number(fourth) + 1 };
  }
  return { startLine, startColumn, endLine: startLine, endColumn: (third ? Number(third) : startColumn) + 1 };
}

export default function App() {
  const initial = useMemo(initialProject, []);
  const [exampleId, setExampleId] = useState(initial.exampleId);
  const [files, setFiles] = useState(initial.files);
  // Monaco keeps one model per path; a new project gets new paths.
  const [generation, setGeneration] = useState(0);
  const [active, setActive] = useState(initial.files[initial.files.length - 1].name);
  const [status, setStatus] = useState({ kind: "loading", text: "Loading the compiler…" });
  const [build, setBuild] = useState(null);
  const [failure, setFailure] = useState(null);
  const [buildTime, setBuildTime] = useState(null);
  const [activeTab, setActiveTab] = useState("expanded");
  const [cursorPosition, setCursorPosition] = useState({ line: 1, col: 0 });
  const [editorWidth, setEditorWidth] = useState(50);
  const [copied, setCopied] = useState(false);
  const editorRef = useRef(null);
  const compilerRef = useRef(null);
  const filesRef = useRef(files);
  const resizing = useRef(false);
  const buildTimer = useRef(null);

  filesRef.current = files;

  useEffect(() => {
    const compiler = createCompiler({
      onReady: () => setStatus({ kind: "ready", text: "Ready" }),
      onResult: (result, ms) => {
        setBuild(result);
        setFailure(null);
        setBuildTime(Math.round(ms));
        setStatus({ kind: "ready", text: "Ready" });
      },
      onFailure: (message) => {
        setFailure(message);
        setBuild(null);
        setStatus({ kind: "loading", text: "Restarting the compiler…" });
      },
    });
    compilerRef.current = compiler;
    compiler.build(filesRef.current);
    return () => compiler.dispose();
  }, []);

  const requestBuild = useCallback((nextFiles, delay) => {
    clearTimeout(buildTimer.current);
    buildTimer.current = setTimeout(() => compilerRef.current?.build(nextFiles), delay);
  }, []);

  const openProject = useCallback(
    (id, nextFiles) => {
      setExampleId(id);
      setFiles(nextFiles);
      setGeneration((value) => value + 1);
      setActive(nextFiles[nextFiles.length - 1].name);
      requestBuild(nextFiles, 0);
    },
    [requestBuild],
  );

  const handleExampleChange = (event) => {
    const example = examples.find((candidate) => candidate.id === event.target.value);
    if (!example) return;
    window.history.replaceState(null, "", window.location.pathname + window.location.search);
    openProject(example.id, example.files);
  };

  const handleEditorChange = useCallback(
    (value) => {
      const nextFiles = filesRef.current.map((file) =>
        file.name === active ? { ...file, source: value ?? "" } : file,
      );
      setFiles(nextFiles);
      requestBuild(nextFiles, 300);
    },
    [active, requestBuild],
  );

  const handleEditorMount = useCallback((editor) => {
    editorRef.current = editor;
    editor.onDidChangeCursorPosition((event) => {
      setCursorPosition({ line: event.position.lineNumber, col: event.position.column - 1 });
    });
  }, []);

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

  const addFile = () => {
    const name = window.prompt("Name of the new file", "Util.res")?.trim();
    if (!name) return;
    if (!/^[A-Za-z][A-Za-z0-9_.-]*$/.test(name)) {
      window.alert("A file name is letters, digits, dots, dashes and underscores.");
      return;
    }
    if (files.some((file) => file.name === name)) {
      window.alert(`There is already a file ${name}.`);
      return;
    }
    const nextFiles = [...files, { name, source: "" }];
    setFiles(nextFiles);
    setActive(name);
    requestBuild(nextFiles, 0);
  };

  const removeFile = (name) => {
    if (files.length === 1) return;
    const nextFiles = files.filter((file) => file.name !== name);
    setFiles(nextFiles);
    if (active === name) setActive(nextFiles[nextFiles.length - 1].name);
    requestBuild(nextFiles, 0);
  };

  const share = async () => {
    const hash = encodeProject(files);
    window.history.replaceState(null, "", hash);
    try {
      await navigator.clipboard.writeText(window.location.href);
      setCopied(true);
      setTimeout(() => setCopied(false), 1500);
    } catch {
      // The link is in the address bar.
    }
  };

  // Resize handle
  useEffect(() => {
    const handleMouseMove = (event) => {
      if (!resizing.current) return;
      const pct = (event.clientX / window.innerWidth) * 100;
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

  const activeFile = files.find((file) => file.name === active) ?? files[0];
  const result = build?.results?.[activeFile.name] ?? null;
  const example = examples.find((candidate) => candidate.id === exampleId);

  // Errors and warnings of every file, in build order.
  const problems = useMemo(() => {
    if (failure) return [{ file: null, kind: "error", message: failure }];
    if (!build) return [];
    const found = [];
    for (const name of build.order) {
      const fileResult = build.results[name];
      if (!fileResult) continue;
      if (fileResult.type === "success") {
        if (fileResult.warnings) found.push({ file: name, kind: "warning", message: fileResult.warnings });
      } else {
        found.push({ file: name, kind: fileResult.type, message: fileResult.message });
      }
    }
    return found;
  }, [build, failure]);

  // Show the first location of each file's messages in its editor.
  useEffect(() => {
    if (!monacoInstance) return;
    for (const file of files) {
      const model = monacoInstance.editor.getModel(monacoInstance.Uri.parse(`${generation}/${file.name}`));
      if (!model) continue;
      const markers = problems
        .filter((problem) => problem.file === file.name && problem.kind !== "skipped")
        .map((problem) => {
          const location = locationOf(problem.message);
          if (!location) return null;
          return {
            severity:
              problem.kind === "warning"
                ? monacoInstance.MarkerSeverity.Warning
                : monacoInstance.MarkerSeverity.Error,
            message: problem.message,
            startLineNumber: location.startLine,
            startColumn: location.startColumn,
            endLineNumber: location.endLine,
            endColumn: location.endColumn,
          };
        })
        .filter(Boolean);
      monacoInstance.editor.setModelMarkers(model, "rescript", markers);
    }
  }, [problems, files, generation]);

  const errorCount = problems.filter((problem) => problem.kind !== "warning").length;

  return (
    <div className="app">
      <header className="header">
        <div className="header-left">
          <a className="back" href="./" title="The RFC, with live examples">
            ← RFC
          </a>
          <h1>ReScript macros</h1>
          <span className="badge">Rust Compiler</span>
          <select className="example-select" value={exampleId} onChange={handleExampleChange}>
            {exampleId === "" && <option value="">Shared project</option>}
            {examples.map((candidate) => (
              <option key={candidate.id} value={candidate.id}>
                {candidate.title}
              </option>
            ))}
          </select>
          {example && <span className="example-summary">{example.summary}</span>}
        </div>
        <div className="header-right">
          <span className={`status ${status.kind}`}>{status.text}</span>
          {buildTime !== null && <span className="compile-time">{buildTime}ms</span>}
          <button className="share-button" onClick={share}>
            {copied ? "Link copied" : "Share"}
          </button>
        </div>
      </header>

      <div className="main">
        <div className="editor-pane" style={{ width: `${editorWidth}%` }}>
          <div className="file-tabs">
            {files.map((file) => {
              const fileResult = build?.results?.[file.name];
              const state = !fileResult ? "" : fileResult.type === "success" ? "ok" : "failed";
              return (
                <div
                  key={file.name}
                  className={`file-tab ${file.name === activeFile.name ? "active" : ""}`}
                  onClick={() => setActive(file.name)}
                >
                  {isSourceFile(file.name) && <span className={`file-state ${state}`} />}
                  <span>{file.name}</span>
                  {files.length > 1 && (
                    <button
                      className="file-close"
                      title={`Remove ${file.name}`}
                      onClick={(event) => {
                        event.stopPropagation();
                        removeFile(file.name);
                      }}
                    >
                      ×
                    </button>
                  )}
                </div>
              );
            })}
            <button className="file-add" title="Add a file" onClick={addFile}>
              +
            </button>
          </div>
          <div className="editor-body">
            <Editor
              path={`${generation}/${activeFile.name}`}
              defaultLanguage={languageOf(activeFile.name)}
              defaultValue={activeFile.source}
              theme="vs-dark"
              onChange={handleEditorChange}
              onMount={handleEditorMount}
              options={EDITOR_OPTIONS}
            />
          </div>
        </div>

        <div className="resize-handle" onMouseDown={handleResizeStart} />

        <div className="output-pane" style={{ flex: 1 }}>
          <Tabs.Root value={activeTab} onValueChange={setActiveTab}>
            <Tabs.List className="tabs-list">
              {TABS.map(([key, label]) => (
                <Tabs.Tab key={key} value={key} className="tabs-tab">
                  {label}
                </Tabs.Tab>
              ))}
              <Tabs.Indicator className="tabs-indicator" />
            </Tabs.List>

            {TABS.map(([key]) => (
              <Tabs.Panel key={key} value={key} className="tabs-panel" keepMounted>
                <Panel
                  tab={key}
                  file={activeFile}
                  result={result}
                  logs={build?.logs ?? null}
                  cursorPosition={cursorPosition}
                  onNodeClick={handleNodeClick}
                />
              </Tabs.Panel>
            ))}
          </Tabs.Root>
          {problems.length > 0 && (
            <div className="problems">
              <div className="problems-title">
                {errorCount > 0 ? `${errorCount} error${errorCount === 1 ? "" : "s"}` : "Warnings"}
              </div>
              {problems.map((problem, index) => (
                <pre
                  key={index}
                  className={`problem ${problem.kind}`}
                  onClick={() => problem.file && setActive(problem.file)}
                >
                  {problem.kind === "skipped" ? `${problem.file}: ${problem.message}` : problem.message}
                </pre>
              ))}
            </div>
          )}
        </div>
      </div>
    </div>
  );
}

function Panel({ tab, file, result, logs, cursorPosition, onNodeClick }) {
  if (tab === "output") return <Output logs={logs} />;
  if (!isSourceFile(file.name)) {
    return <div className="empty-panel">{file.name} is not compiled. A macro can read it with Macro.readFile.</div>;
  }
  if (!result) return <div className="empty-panel">Compiling…</div>;
  if (tab === "expanded") {
    if (result.type !== "success") return <div className="empty-panel">This file did not compile.</div>;
    if (!result.expanded) {
      return (
        <div className="panel-with-note">
          <div className="panel-note">This file uses no macro, so it is compiled as written.</div>
          <ReadOnly language={languageId} value={file.source} />
        </div>
      );
    }
    return (
      <div className="panel-with-note">
        <div className="panel-note">The source after macro expansion: what the compiler compiles.</div>
        <ReadOnly language={languageId} value={result.expanded} />
      </div>
    );
  }
  if (tab === "js") {
    if (result.type !== "success") return <div className="empty-panel">This file did not compile.</div>;
    return <ReadOnly language="javascript" value={result.js} />;
  }
  const sexp = result[tab];
  if (!sexp) return <div className="empty-panel">No data</div>;
  return <TreeView sexp={sexp} cursorPosition={cursorPosition} onNodeClick={onNodeClick} />;
}

function Output({ logs }) {
  if (logs === null) return <div className="empty-panel">The program runs when every file compiles.</div>;
  if (logs.length === 0) return <div className="empty-panel">The program printed nothing.</div>;
  return (
    <div className="console">
      {logs.map((log, index) => (
        <pre key={index} className={`console-line ${log.level}`}>
          {log.text}
        </pre>
      ))}
    </div>
  );
}

function ReadOnly({ language, value }) {
  return (
    <div className="js-output">
      <Editor language={language} value={value} theme="vs-dark" options={READONLY_OPTIONS} />
    </div>
  );
}
