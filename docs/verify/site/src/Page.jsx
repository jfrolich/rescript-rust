import React, { useEffect, useMemo, useState } from "react";
import { examples } from "./examples.js";
import prebuilt from "./prebuilt.json";
import { Example } from "./Example.jsx";
import { headings, lex, Markdown, segments } from "./Markdown.jsx";
import { warmUp } from "./compiler.js";

const REPOSITORY = "https://github.com/jfrolich/rescript-rust";
// Filled in by the build: see vite.config.js.
const PULL_REQUEST = import.meta.env.VITE_PULL_REQUEST || null;

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
 * The document, with its examples live. `about` says where the document is
 * in the repository and what the page shows around it: `doc` (its
 * directory), `branch`, `pullRequest`, `status` (the second chip), `jump` (a
 * link into the page), `pages` (documents of the directory that have a page
 * of their own, by file name) and `colophon`.
 */
export function Page({ markdown, title, lede, about }) {
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

  // A relative link is a file of the repository, relative to the document.
  const links = (href) => {
    if (href.startsWith("#") || /^[a-z]+:/.test(href)) return href;
    if (about.pages?.[href]) return about.pages[href];
    const path = new URL(href, `https://x/${about.doc}/`).pathname.slice(1);
    return `${REPOSITORY}/blob/${about.branch}/${path}`;
  };
  const pullRequest = about.pullRequest ?? PULL_REQUEST;
  const github = pullRequest
    ? `${REPOSITORY}/pull/${pullRequest}`
    : `${REPOSITORY}/tree/${about.branch}/${about.doc}`;
  const source = { href: github, text: pullRequest ? `Pull request #${pullRequest} ↗` : "Source ↗" };

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
          <a className="on" href="./">
            RFC
          </a>
          <a href={github} target="_blank" rel="noreferrer">
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
          <span className="chip">{about.status}</span>
          <a className="chip" href={source.href} target="_blank" rel="noreferrer">
            {source.text}
          </a>
          {about.jump && (
            <a className="chip" href={about.jump.href}>
              {about.jump.text}
            </a>
          )}
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
            const example = examples.find((candidate) => candidate.id === part.id);
            if (!example) return null;
            return <Example key={index} example={example} prebuilt={prebuilt[example.id]} />;
          })}
          <footer className="colophon">
            <p>
              This page is <code>{about.doc}</code> of{" "}
              <a href={REPOSITORY} target="_blank" rel="noreferrer">
                the Rust port of the ReScript compiler
              </a>
              . {about.colophon}
            </p>
          </footer>
        </main>
      </div>
    </>
  );
}
