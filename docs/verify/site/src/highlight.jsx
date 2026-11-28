/** Static syntax highlighting with the editor's languages. */
import React from "react";
import { highlightTree, classHighlighter } from "@lezer/highlight";
import { javascriptLanguage, typescriptLanguage } from "@codemirror/lang-javascript";
import { jsonLanguage } from "@codemirror/lang-json";
import { rescript } from "./rescript-mode.js";

const languages = {
  rescript,
  res: rescript,
  js: javascriptLanguage,
  javascript: javascriptLanguage,
  ts: typescriptLanguage,
  typescript: typescriptLanguage,
  json: jsonLanguage,
};

export function languageOf(filename) {
  if (filename.endsWith(".res") || filename.endsWith(".resi")) return "rescript";
  if (filename.endsWith(".json")) return "json";
  if (filename.endsWith(".ts") || filename.endsWith(".tsx")) return "typescript";
  if (filename.endsWith(".js") || filename.endsWith(".mjs")) return "javascript";
  return "text";
}

export function codemirrorLanguage(name) {
  return languages[name] ?? null;
}

/** `code` as an array of React nodes, with a class on each token. */
export function highlight(code, languageName) {
  const language = languages[languageName];
  if (!language) return [code];
  const nodes = [];
  let position = 0;
  highlightTree(language.parser.parse(code), classHighlighter, (from, to, classes) => {
    if (from > position) nodes.push(code.slice(position, from));
    nodes.push(
      <span key={from} className={classes}>
        {code.slice(from, to)}
      </span>,
    );
    position = to;
  });
  if (position < code.length) nodes.push(code.slice(position));
  return nodes;
}

/** The highlighted nodes, split into lines. */
function lines(nodes) {
  const out = [[]];
  nodes.forEach((node, index) => {
    const text = typeof node === "string" ? node : node.props.children;
    const parts = text.split("\n");
    parts.forEach((part, partIndex) => {
      if (partIndex > 0) out.push([]);
      if (part === "") return;
      out[out.length - 1].push(
        typeof node === "string" ? (
          part
        ) : (
          <span key={`${index}/${partIndex}`} className={node.props.className}>
            {part}
          </span>
        ),
      );
    });
  });
  if (out.length > 1 && out[out.length - 1].length === 0) out.pop();
  return out;
}

/**
 * The lines of `after` that are not lines of `before`, by a longest common
 * subsequence of the two, as a set of line numbers counted from zero.
 */
export function addedLines(before, after) {
  const a = before.split("\n").map((line) => line.trim());
  const b = after.split("\n").map((line) => line.trim());
  const width = b.length + 1;
  const table = new Uint16Array((a.length + 1) * width);
  for (let i = a.length - 1; i >= 0; i--) {
    for (let j = b.length - 1; j >= 0; j--) {
      table[i * width + j] =
        a[i] === b[j] ? table[(i + 1) * width + j + 1] + 1 : Math.max(table[(i + 1) * width + j], table[i * width + j + 1]);
    }
  }
  const added = new Set();
  let i = 0;
  let j = 0;
  while (j < b.length) {
    if (i < a.length && a[i] === b[j]) {
      i++;
      j++;
    } else if (i < a.length && table[(i + 1) * width + j] >= table[i * width + j + 1]) {
      i++;
    } else {
      if (b[j] !== "") added.add(j);
      j++;
    }
  }
  return added;
}

/** `marked` is a set of line numbers to set apart, counted from zero. */
export function Code({ code, language, className = "", marked = null }) {
  const nodes = React.useMemo(() => highlight(code, language), [code, language]);
  if (!marked || marked.size === 0) {
    return (
      <pre className={`code ${className}`}>
        <code>{nodes}</code>
      </pre>
    );
  }
  return (
    <pre className={`code lined ${className}`}>
      <code>
        {lines(nodes).map((line, index) => (
          <span key={index} className={marked.has(index) ? "line marked" : "line"}>
            {line}
            {"\n"}
          </span>
        ))}
      </code>
    </pre>
  );
}
