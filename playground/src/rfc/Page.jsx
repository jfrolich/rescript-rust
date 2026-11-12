import React, { useEffect, useMemo, useState } from "react";
import { examples } from "../examples.js";
import prebuilt from "./prebuilt.json";
import session from "../../examples/repl.json";
import { sessionLibraries } from "../repl-transcript.js";
import { Example } from "./Example.jsx";
import { Repl } from "./Repl.jsx";
import { CostChart } from "./Diagrams.jsx";
import { headings, lex, Markdown, segments } from "./Markdown.jsx";
import { warmUp } from "./compiler.js";

const REPOSITORY = "https://github.com/jfrolich/rescript-rust";

// The modules a session of the read-eval-print loop starts with.
const libraries = sessionLibraries(examples);

function useTheme() {
  const [theme, setTheme] = useState(() => localStorage.getItem("theme") ?? "auto");
  useEffect(() => {
    if (theme === "auto") delete document.documentElement.dataset.theme;
    else document.documentElement.dataset.theme = theme;
    localStorage.setItem("theme", theme);
  }, [theme]);
  const dark =
    theme === "dark" || (theme === "auto" && window.matchMedia("(prefers-color-scheme: dark)").matches);
  return [dark, () => setTheme(dark ? "light" : "dark")];
}

/** The heading the reader is under, for the table of contents. */
function useActiveHeading(ids) {
  const [active, setActive] = useState(ids[0]);
  useEffect(() => {
    const update = () => {
      let current = ids[0];
      for (const id of ids) {
        const element = document.getElementById(id);
        if (element && element.getBoundingClientRect().top < 120) current = id;
      }
      setActive(current);
    };
    update();
    window.addEventListener("scroll", update, { passive: true });
    return () => window.removeEventListener("scroll", update);
  }, [ids]);
  return active;
}

/**
 * One document of the RFC. `pages` maps the file name of a sibling
 * document to its page.
 */
export function Page({ markdown, title, lede, pages, current }) {
  const [dark, toggleTheme] = useTheme();
  const parts = useMemo(() => {
    // The page has its own title and table of contents.
    const body = markdown.replace(/^# .*\n/, "").replace(/\n(- \[[^\]]+\]\(#[^)]+\)\n)+/, "\n");
    return segments(body).map((segment) =>
      segment.type === "markdown" ? { ...segment, tokens: lex(segment.text) } : segment,
    );
  }, [markdown]);
  const toc = useMemo(() => headings(markdown), [markdown]);
  const ids = useMemo(() => toc.map((entry) => entry.id), [toc]);
  const active = useActiveHeading(ids);
  const activeSection = toc.find((entry) => entry.id === active)?.section;

  // Load the compiler once the page has settled, so the first edit is quick.
  useEffect(() => {
    if (!parts.some((part) => part.type === "example")) return undefined;
    const timer = setTimeout(warmUp, 2500);
    return () => clearTimeout(timer);
  }, [parts]);

  const links = (href) => {
    if (pages[href]) return pages[href];
    if (!href.startsWith("#") && !/^[a-z]+:/.test(href)) return `${REPOSITORY}/blob/comptime-macros/docs/comptime/${href}`;
    return href;
  };

  return (
    <>
      <header className="topbar">
        <a className="brand" href="/" aria-label="Submodule">
          <svg viewBox="0 0 32 32" aria-hidden="true">
            <path d="M5 10.5 16 4l11 6.5v11L16 28 5 21.5Z" />
            <path d="m5 10.5 11 6.3 11-6.3M16 16.8V28" />
          </svg>
          <span>Submodule</span>
        </a>
        <nav>
          <a className={current === "rfc" ? "on" : ""} href="./">
            RFC
          </a>
          <a className={current === "implementation" ? "on" : ""} href="implementation.html">
            Implementation
          </a>
          <a href="playground.html">Playground</a>
          <a href={`${REPOSITORY}/pull/90`} target="_blank" rel="noreferrer">
            GitHub ↗
          </a>
          <button type="button" className="theme" onClick={toggleTheme} aria-label="Switch between light and dark">
            {dark ? "☀" : "☾"}
          </button>
        </nav>
      </header>

      <div className="hero">
        <p className="eyebrow">
          <span />
          ReScript · request for comments
        </p>
        <h1>{title}</h1>
        <p className="lede">{lede}</p>
        <div className="hero-meta">
          <span className="chip solid">Draft</span>
          <span className="chip">Implemented on a branch</span>
          <a className="chip" href={`${REPOSITORY}/pull/90`} target="_blank" rel="noreferrer">
            Pull request #90 ↗
          </a>
          <a className="chip" href="playground.html">
            Open the playground →
          </a>
        </div>
      </div>

      <div className="layout">
        <aside className="toc" aria-label="Contents">
          <div className="toc-title">Contents</div>
          {toc
            .filter((entry) => entry.depth === 2 || entry.section === activeSection)
            .map((entry) => (
              <a
                key={entry.id}
                href={`#${entry.id}`}
                className={[
                  entry.depth === 3 ? "sub" : "",
                  entry.id === active || (entry.depth === 2 && entry.id === activeSection) ? "on" : "",
                ].join(" ")}
              >
                {entry.text}
              </a>
            ))}
        </aside>
        <main className="prose">
          {parts.map((part, index) => {
            if (part.type === "markdown") return <Markdown key={index} tokens={part.tokens} links={links} />;
            if (part.type === "chart") return <CostChart key={index} />;
            if (part.type === "repl") {
              return <Repl key={index} libraries={libraries} intro={prebuilt.$repl ?? []} tries={session.tries} />;
            }
            const example = examples.find((candidate) => candidate.id === part.id);
            if (!example) return null;
            return <Example key={index} example={example} prebuilt={prebuilt[example.id]} />;
          })}
          <footer className="colophon">
            <p>
              This page is <code>docs/comptime</code> of{" "}
              <a href={REPOSITORY} target="_blank" rel="noreferrer">
                the Rust port of the ReScript compiler
              </a>
              . The examples are compiled in your browser by that compiler, built to WebAssembly.
            </p>
          </footer>
        </main>
      </div>
    </>
  );
}
