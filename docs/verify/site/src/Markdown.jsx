/** Renders the RFC's Markdown as React elements. */
import React from "react";
import { marked } from "marked";
import { Code } from "./highlight.jsx";

export function slug(text) {
  return text
    .toLowerCase()
    .replace(/[^\w\s-]/g, "")
    .trim()
    .replace(/\s+/g, "-");
}

function plain(tokens) {
  return (tokens ?? [])
    .map((token) => (token.tokens ? plain(token.tokens) : token.text ?? token.raw ?? ""))
    .join("");
}

function decode(text) {
  return text
    .replace(/&amp;/g, "&")
    .replace(/&lt;/g, "<")
    .replace(/&gt;/g, ">")
    .replace(/&quot;/g, '"')
    .replace(/&#39;/g, "'");
}

function inline(tokens, links) {
  return (tokens ?? []).map((token, index) => {
    switch (token.type) {
      case "strong":
        return <strong key={index}>{inline(token.tokens, links)}</strong>;
      case "em":
        return <em key={index}>{inline(token.tokens, links)}</em>;
      case "codespan":
        return <code key={index}>{decode(token.text)}</code>;
      case "br":
        return <br key={index} />;
      case "del":
        return <del key={index}>{inline(token.tokens, links)}</del>;
      case "link": {
        const href = links(token.href);
        const external = /^https?:/.test(href);
        return (
          <a key={index} href={href} {...(external ? { target: "_blank", rel: "noreferrer" } : {})}>
            {inline(token.tokens, links)}
          </a>
        );
      }
      case "html":
        return null;
      default:
        return token.tokens ? (
          <React.Fragment key={index}>{inline(token.tokens, links)}</React.Fragment>
        ) : (
          decode(token.text ?? token.raw)
        );
    }
  });
}

function block(token, index, links) {
  switch (token.type) {
    case "heading": {
      const Tag = `h${token.depth}`;
      const id = slug(plain(token.tokens));
      return (
        <Tag key={index} id={id}>
          <a className="anchor" href={`#${id}`} aria-hidden="true" tabIndex={-1}>
            #
          </a>
          {inline(token.tokens, links)}
        </Tag>
      );
    }
    case "paragraph":
      return <p key={index}>{inline(token.tokens, links)}</p>;
    case "code": {
      return <Code key={index} code={token.text} language={token.lang || "text"} className={token.lang ? "" : "plain"} />;
    }
    case "list": {
      const Tag = token.ordered ? "ol" : "ul";
      return (
        <Tag key={index}>
          {token.items.map((item, itemIndex) => (
            <li key={itemIndex}>
              {item.tokens.map((child, childIndex) =>
                child.type === "text" ? (
                  <React.Fragment key={childIndex}>{inline(child.tokens ?? [child], links)}</React.Fragment>
                ) : (
                  block(child, childIndex, links)
                ),
              )}
            </li>
          ))}
        </Tag>
      );
    }
    case "table":
      return (
        <div key={index} className="table-wrap">
          <table>
            <thead>
              <tr>
                {token.header.map((cell, cellIndex) => (
                  <th key={cellIndex}>{inline(cell.tokens, links)}</th>
                ))}
              </tr>
            </thead>
            <tbody>
              {token.rows.map((row, rowIndex) => (
                <tr key={rowIndex}>
                  {row.map((cell, cellIndex) => (
                    <td key={cellIndex}>{inline(cell.tokens, links)}</td>
                  ))}
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      );
    case "blockquote":
      return <blockquote key={index}>{token.tokens.map((child, childIndex) => block(child, childIndex, links))}</blockquote>;
    case "hr":
      return <hr key={index} />;
    default:
      return null;
  }
}

/**
 * Split the document at its markers. `<!-- example: id -->` up to
 * `<!-- /example -->` is replaced by the live example; the static code in
 * between is what other renderers show.
 */
export function segments(markdown) {
  const out = [];
  const marker = /<!-- example: ([\w-]+) -->[\s\S]*?<!-- \/example -->/g;
  let position = 0;
  for (const match of markdown.matchAll(marker)) {
    if (match.index > position) out.push({ type: "markdown", text: markdown.slice(position, match.index) });
    out.push({ type: "example", id: match[1] });
    position = match.index + match[0].length;
  }
  if (position < markdown.length) out.push({ type: "markdown", text: markdown.slice(position) });
  return out;
}

export function lex(text) {
  return marked.lexer(text);
}

/** The second and third level headings, each with the section it is in. */
export function headings(markdown) {
  let section = null;
  return lex(markdown.replace(/<!--[\s\S]*?-->/g, ""))
    .filter((token) => token.type === "heading" && (token.depth === 2 || token.depth === 3))
    .map((token) => {
      const text = plain(token.tokens);
      const id = slug(text);
      if (token.depth === 2) section = id;
      return { depth: token.depth, text, id, section };
    });
}

export function Markdown({ tokens, links = (href) => href }) {
  return <>{tokens.map((token, index) => block(token, index, links))}</>;
}
