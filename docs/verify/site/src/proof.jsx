import React from "react";
import { createRoot } from "react-dom/client";
import document from "../../proof.md?raw";
import { Page } from "./Page.jsx";
import { about } from "./about.jsx";
import "./rfc.css";

createRoot(window.document.getElementById("root")).render(
  <Page
    markdown={document}
    title={
      <>
        <em>Proofs</em>: laws shown for every value
      </>
    }
    lede="A thousand lists that satisfy a law are evidence, not all lists. rescript verify now tries to prove each law from its code: it computes with unknowns, splits into cases, uses induction on lists and trees, and uses the laws proved before. There is no proof to write, and what it cannot prove it still runs. Every example on this page is live: the proofs are found in your browser."
    about={{ ...about, pullRequest: 271, jump: { href: "#reference", text: "The rules →" } }}
  />,
);
