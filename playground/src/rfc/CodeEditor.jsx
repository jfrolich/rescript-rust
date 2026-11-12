import React, { useEffect, useRef } from "react";
import { EditorState } from "@codemirror/state";
import { EditorView, keymap, drawSelection, highlightSpecialChars } from "@codemirror/view";
import { defaultKeymap, history, historyKeymap, indentWithTab } from "@codemirror/commands";
import { bracketMatching, indentOnInput, indentUnit, syntaxHighlighting } from "@codemirror/language";
import { acceptCompletion, closeBrackets, closeBracketsKeymap } from "@codemirror/autocomplete";
import { classHighlighter } from "@lezer/highlight";
import { codemirrorLanguage } from "./highlight.jsx";
import { completion } from "./completion.js";

/**
 * An editor for one file. The document is created from `value` once: the
 * parent gives the editor a new `key` to replace it. With `complete`, the
 * editor offers completions.
 */
export function CodeEditor({ value, language, onChange, onCursor, onFocus, complete, viewRef }) {
  const host = useRef(null);
  const handlers = useRef({ onChange, onCursor, onFocus, complete });
  handlers.current = { onChange, onCursor, onFocus, complete };

  useEffect(() => {
    const languageExtension = codemirrorLanguage(language);
    const view = new EditorView({
      parent: host.current,
      state: EditorState.create({
        doc: value,
        extensions: [
          highlightSpecialChars(),
          history(),
          drawSelection(),
          indentOnInput(),
          bracketMatching(),
          closeBrackets(),
          indentUnit.of("  "),
          EditorState.tabSize.of(2),
          syntaxHighlighting(classHighlighter),
          languageExtension ? [languageExtension] : [],
          // The compiler completes ReScript: `complete(source, offset, explicit)`.
          language === "rescript" && complete
            ? completion((...request) => handlers.current.complete?.(...request) ?? Promise.resolve(null))
            : [],
          keymap.of([
            { key: "Tab", run: acceptCompletion },
            ...closeBracketsKeymap,
            ...defaultKeymap,
            ...historyKeymap,
            indentWithTab,
          ]),
          EditorView.updateListener.of((update) => {
            if (update.docChanged) handlers.current.onChange?.(update.state.doc.toString());
            if (update.selectionSet || update.docChanged) {
              const head = update.state.selection.main.head;
              const line = update.state.doc.lineAt(head);
              handlers.current.onCursor?.({ line: line.number, col: head - line.from });
            }
            if (update.focusChanged && update.view.hasFocus) handlers.current.onFocus?.();
          }),
          EditorView.contentAttributes.of({ "aria-label": "Source code", spellcheck: "false" }),
        ],
      }),
    });
    if (viewRef) viewRef.current = view;
    return () => {
      if (viewRef && viewRef.current === view) viewRef.current = null;
      view.destroy();
    };
    // The document is not synchronized with `value` after creation.
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [language]);

  return <div className="editor" ref={host} />;
}

/** Select a range given as 1-based lines and 0-based columns. */
export function selectRange(view, loc) {
  if (!view || !loc) return;
  const doc = view.state.doc;
  const position = (line, col) => {
    const info = doc.line(Math.max(1, Math.min(doc.lines, line)));
    return Math.min(info.to, info.from + col);
  };
  view.dispatch({
    selection: { anchor: position(loc.startLine, loc.startCol), head: position(loc.endLine, loc.endCol) },
    scrollIntoView: true,
  });
  view.focus();
}
