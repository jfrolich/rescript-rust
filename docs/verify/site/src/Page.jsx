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
 * of their own, by file name), `series` (the RFCs the pages are, in order),
 * `current` (which of them this page is, or `"overview"`) and `colophon`.
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
  const index = about.series?.findIndex((rfc) => rfc.page === about.current) ?? -1;
  const position = index >= 0 ? { index, previous: about.series[index - 1], next: about.series[index + 1] } : null;

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
          <a className={about.current === "overview" ? "on" : ""} href="./">
            Series
          </a>
          <a href={github} target="_blank" rel="noreferrer">
            GitHub ↗
          </a>
          <button type="button" className="theme" onClick={toggleTheme} aria-label="Switch between light and dark">
            {dark ? "☀" : "☾"}
          </button>
        </nav>
      </header>

      {about.series && <SeriesBar series={about.series} current={about.current} />}

      <div className="hero">
        <p className="eyebrow">
          <span />
          {position ? `Verification · RFC ${position.index + 1} of ${about.series.length}` : about.current === "overview"
              ? `Verification · a series of ${about.series.length} RFCs`
              : "ReScript · request for comments"}
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
          {about.current === "overview" && about.series && <SeriesCards series={about.series} />}
          {parts.map((part, index) => {
            if (part.type === "markdown") return <Markdown key={index} tokens={part.tokens} links={links} />;
            const example = examples.find((candidate) => candidate.id === part.id);
            if (!example) return null;
            return <Example key={index} example={example} prebuilt={prebuilt[example.id]} />;
          })}
          {position && <SeriesNext previous={position.previous} next={position.next} />}
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

/** The RFCs of the series, with the one this page is marked. */
function SeriesBar({ series, current }) {
  // On a narrow screen the strip scrolls: show the RFC this page is.
  useEffect(() => {
    document.querySelector(".series ol a.on")?.scrollIntoView({ block: "nearest", inline: "nearest" });
  }, []);
  return (
    <nav className="series" aria-label="The verification RFCs">
      <div className="series-inner">
        <a className={current === "overview" ? "series-home on" : "series-home"} href="./">
          Verification series
        </a>
        <ol>
          {series.map((rfc, index) => (
            <li key={rfc.page}>
              <a
                href={rfc.href}
                className={rfc.page === current ? "on" : ""}
                aria-current={rfc.page === current ? "page" : undefined}
              >
                <span className="series-number">{index + 1}</span>
                <span className="series-name">{rfc.name}</span>
                <span className="series-adds">{rfc.adds}</span>
              </a>
            </li>
          ))}
        </ol>
      </div>
    </nav>
  );
}

/** The series on the overview page: one card per RFC, in reading order. */
function SeriesCards({ series }) {
  return (
    <ol className="series-cards">
      {series.map((rfc, index) => (
        <li key={rfc.page}>
          <a href={rfc.href}>
            <span className="series-card-number">RFC {index + 1}</span>
            <span className="series-card-name">{rfc.name}</span>
            <code className="series-card-adds">{rfc.adds}</code>
            <span className="series-card-summary">{rfc.summary}</span>
            <span className="series-card-checked">
              <span>Checked {rfc.checked}</span>
              <span>Read →</span>
            </span>
          </a>
        </li>
      ))}
    </ol>
  );
}

/** Where to go from the end of an RFC: the one before it and the one after. */
function SeriesNext({ previous, next }) {
  return (
    <nav className="series-next" aria-label="Previous and next RFC">
      {previous ? (
        <a className="previous" href={previous.href}>
          <span>← Previous</span>
          <strong>{previous.name}</strong>
          <em>{previous.adds}</em>
        </a>
      ) : (
        <a className="previous" href="./">
          <span>← The series</span>
          <strong>Overview</strong>
          <em>all four RFCs</em>
        </a>
      )}
      {next ? (
        <a className="next" href={next.href}>
          <span>Next →</span>
          <strong>{next.name}</strong>
          <em>{next.adds}</em>
        </a>
      ) : (
        <a className="next" href="./">
          <span>The series →</span>
          <strong>Overview</strong>
          <em>all four RFCs</em>
        </a>
      )}
    </nav>
  );
}
